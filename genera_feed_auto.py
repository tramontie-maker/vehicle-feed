# =============================================================================
# GENERA FEED AUTO — Auto Occasioni Milano
# =============================================================================
# Legge i listing dal sito via REST API, fa scraping di prezzo e km,
# esclude le auto vendute e genera due feed XML:
#   - feed_auto_google.xml   (Google Vehicle Ads)
#   - feed_auto_facebook.xml (Meta Automotive Inventory Ads)
#
# Gira su GitHub Actions (.github/workflows/feed.yml): il salvataggio dei file
# lo fa il workflow, non questo script. Se un controllo fallisce non scrive
# niente ed esce con errore. Il repo è pubblico: nei registri solo conteggi.
#
# COME USARLO:
#   python3 genera_feed_auto.py
#
# OUTPUT (accanto allo script):
#   feed_auto_google.xml, feed_auto_facebook.xml, esclusi.txt
#
# DIPENDENZE:
#   pip install requests
# =============================================================================

import re
import time
import os
import sys
import html as htmllib
from datetime import datetime
from xml.etree.ElementTree import Element, SubElement, ElementTree, indent, parse

try:
    import requests
except ImportError:
    print("❌ Libreria 'requests' non trovata. Esegui: pip install requests")
    sys.exit(1)

# =============================================================================
# COSTANTI
# =============================================================================

API_BASE    = "https://www.autoccasionimilano.it/wp-json/wp/v2"
STORE_NAME  = "Auto Occasioni Milano"
STORE_URL   = "https://www.autoccasionimilano.it"
OUTPUT_DIR  = os.path.dirname(os.path.abspath(__file__))
CURRENCY        = "EUR"
CONDITION       = "used"
GOOGLE_CATEGORY = "916"  # ID tassonomia Google: "Veicoli e parti > Veicoli > Veicoli per terraferma > Auto, autocarri e furgoni"
STORE_CODE      = "12756304075837814277"  # Codice negozio Google Business Profile (sede Via Sangro 10) — letto da GBP API il 2026-05-09
PAUSA_SEC       = 1.5  # secondi tra una richiesta di scraping e l'altra
MAX_ESCLUSE     = 0.20  # oltre questa quota di auto escluse il feed non si scrive

HEADERS = {"User-Agent": "Mozilla/5.0 (compatible; FeedBot/1.0)"}

# Segni di una pagina di verifica o blocco al posto del contenuto vero
BLOCCO_PATTERNS = re.compile(
    r"just a moment|attention required|verify you are human|cf-chl|captcha"
    r"|access denied|accesso negato|request blocked|sucuri website firewall",
    re.IGNORECASE
)
BLOCCO_STATUS = (401, 403, 429, 503)

# Pattern label API che indicano auto non disponibile
SOLD_LABEL_PATTERNS = re.compile(
    r"vendut|non.disponib|riservat|esaurit", re.IGNORECASE
)
# Pattern HTML più specifici — evita falsi positivi da footer/copyright
SOLD_HTML_PATTERNS = re.compile(
    r"auto\s+venduta|auto\s+non\s+disponib|sold.out|questa\s+auto\s+non|prenotato", re.IGNORECASE
)

# Mappatura valori IT → EN per Google Vehicle Ads spec (enum chiusi lowercase)
FUEL_MAP = {
    "benzina":              "gasoline",
    "diesel":               "diesel",
    "ibrida":               "hybrid",
    "elettrica / benzina":  "hybrid",
    "elettrica / diesel":   "hybrid",
    "elettrica":            "electric",
    "gpl":                  "lpg",
    "metano":               "methane",
    "ibrida plug-in":       "plug-in_hybrid",
}
TRANSMISSION_MAP = {
    "automatico":     "automatic",
    "manuale":        "manual",
    "semiautomatico": "semi-automatic",
}
BODY_STYLE_MAP = {
    "berlina":        "sedan",
    "city car":       "city_car",
    "monovolume":     "minivan",
    "suv":            "suv",
    "station wagon":  "station_wagon",
    "coupé":          "coupe",
    "coupe":          "coupe",
    "cabrio":         "convertible",
    "cabriolet":      "convertible",
    "hatchback":      "hatchback",
    "crossover":      "crossover",
    "fuoristrada":    "suv",
    "pickup":         "truck",
    "furgone":        "full_size_van",
}


# =============================================================================
# FUNZIONI UTILITY
# =============================================================================

def traduci_o_log(valore, mappa, attributo, auto_id):
    """Traduce IT → EN; se non mappato logga un warning e ritorna stringa vuota."""
    if not valore:
        return ""
    en = mappa.get(valore.strip().lower())
    if en is None:
        print(f"   ⚠️  {attributo}={valore!r} non mappato (auto {auto_id}) — omesso dal feed")
        return ""
    return en


def normalizza_prezzo(stringa):
    """Converte prezzi in formato italiano/HTML in float.

    Regole (formato sito autoccasionimilano.it):
      - Solo virgola:  '6,980' / '22,990'  → virgola = migliaia → 6980.00 / 22990.00
      - Solo punto:    '6.980' / '22.990'  → punto = migliaia  → 6980.00 / 22990.00
      - Punto + virgola: '7.790,00'        → punto=migliaia, virgola=decimali → 7790.00
    I prezzi sul sito sono sempre interi (no centesimi reali).
    """
    if not stringa:
        return None
    s = stringa.strip().replace(" ", "").replace("€", "").strip()

    if "." in s and "," in s:
        # Formato misto tipo '7.790,00': punto=migliaia, virgola=decimali
        s = s.replace(".", "").replace(",", ".")
    elif "," in s:
        # Solo virgola: sempre separatore migliaia ('6,980' → '6980')
        s = s.replace(",", "")
    elif "." in s:
        # Solo punto: sempre separatore migliaia ('6.980' → '6980')
        s = s.replace(".", "")

    try:
        v = float(s)
        return v if v >= 500 else None  # scarta valori anomali (rate €199, risparmi €600, ecc.)
    except ValueError:
        return None


def normalizza_km(stringa):
    """Converte '86.000' o '86,000' in int 86000"""
    if not stringa:
        return None
    s = re.sub(r"[^\d]", "", stringa)
    try:
        v = int(s)
        return v if v > 100 else None  # esclude valori anomali tipo "100"
    except ValueError:
        return None


ANNO_IMMATR_PAT = re.compile(r">Anno</th>\s*<td[^>]*>\s*(\d{1,2})\s*/\s*(\d{4})", re.IGNORECASE)

def estrai_anno(slug, html):
    """Cerca anno di prima immatricolazione nel template del sito.
    Pattern atteso nella tabella scheda tecnica: <tr><th>Anno</th><td>MM/YYYY</td></tr>
    (es. 'Anno 01/2017'). Lo slug NON è affidabile (es. 'spark-...-2033' = scadenza GPL).
    Ritorna stringa 'YYYY' o '' se non trovato.
    """
    match = ANNO_IMMATR_PAT.search(html)
    return match.group(2) if match else ""

def estrai_data_immatricolazione(html):
    """Stesso pattern di estrai_anno ma ritorna 'YYYY-MM' per date_first_registered."""
    match = ANNO_IMMATR_PAT.search(html)
    if not match:
        return ""
    mese = match.group(1).zfill(2)
    return f"{match.group(2)}-{mese}"


def blocca(motivo):
    """Ferma tutto: nessun file viene scritto e il workflow risulta fallito."""
    print(f"❌ FEED NON GENERATO: {motivo}")
    sys.exit(1)


def richiesta(url, params=None):
    """GET con un secondo tentativo. Ritorna la risposta o None se irraggiungibile."""
    r = None
    for tentativo in (1, 2):
        try:
            r = requests.get(url, params=params, headers=HEADERS, timeout=30)
            if r.status_code < 500:
                return r
        except requests.RequestException:
            r = None
        if tentativo == 1:
            time.sleep(5)
    return r


def controlla_blocco(r):
    """Ferma il feed se la risposta è una pagina di verifica o blocco."""
    if r.status_code in BLOCCO_STATUS or BLOCCO_PATTERNS.search(r.text[:5000]):
        blocca("il sito ha risposto con una pagina di verifica o blocco")


def pulisci_testo(html_str):
    """Rimuove tag HTML e normalizza spazi"""
    clean = re.sub(r"<[^>]+>", " ", html_str)
    clean = re.sub(r"\s+", " ", clean).strip()
    return clean


# =============================================================================
# LETTURA LISTINGS VIA REST API
# =============================================================================

def leggi_listings_api():
    """
    Legge tutti i listing pubblicati dal sito via WP REST API.
    Restituisce lista di dict con campi base + tassonomie + foto.
    """
    print("📡 Lettura listings da REST API...")
    url = f"{API_BASE}/listing"
    data = []
    pagina = 1
    while True:
        params = {"per_page": 100, "_embed": 1, "status": "publish", "page": pagina}
        r = richiesta(url, params)
        if r is None:
            blocca("API del sito non raggiungibile")
        controlla_blocco(r)
        if r.status_code != 200 or "json" not in r.headers.get("Content-Type", ""):
            blocca("API del sito con risposta non valida")
        try:
            data.extend(r.json())
            totale = int(r.headers["X-WP-Total"])
            pagine = int(r.headers["X-WP-TotalPages"])
        except (ValueError, KeyError):
            blocca("API del sito con risposta non valida")
        if pagina >= pagine:
            break
        pagina += 1

    if len({p["id"] for p in data}) != totale or len(data) != totale:
        blocca("API del sito: auto lette diverse dal totale dichiarato")
    print(f"   → {totale} listings trovati nell'API ({pagine} pagine)")

    listings = []
    for p in data:
        embedded = p.get("_embedded", {})

        # Foto principale
        foto_url = ""
        media_list = embedded.get("wp:featuredmedia", [])
        if media_list:
            foto_url = media_list[0].get("source_url", "")

        # Tassonomie (marca, tipo, carburante, ecc.)
        taxa = {}
        for gruppo in embedded.get("wp:term", []):
            for t in gruppo:
                tax = t.get("taxonomy", "")
                nome = t.get("name", "")
                slug_tax = t.get("slug", "")
                taxa[tax] = {"nome": nome, "slug": slug_tax}

        # Etichetta — usata per rilevare auto vendute via API
        label = taxa.get("listing_label", {}).get("nome", "")

        listings.append({
            "id":           str(p["id"]),
            "title":        htmllib.unescape(pulisci_testo(p.get("title", {}).get("rendered", ""))),
            "slug":         p.get("slug", ""),
            "link":         p.get("link", ""),
            "foto_url":     foto_url,
            "marca":        taxa.get("listing_make", {}).get("nome", ""),
            "tipo":         taxa.get("listing_type", {}).get("nome", ""),
            "carburante":   taxa.get("listing_fuel_type", {}).get("nome", ""),
            "cambio":       taxa.get("listing_transmission", {}).get("nome", ""),
            "colore":       taxa.get("listing_color", {}).get("nome", ""),
            "porte":        taxa.get("listing_door", {}).get("nome", ""),
            "condizione":   taxa.get("listing_condition", {}).get("nome", ""),
            "trazione":     taxa.get("listing_drive_type", {}).get("nome", ""),
            "label":        label,
            # Campi da completare con scraping
            "prezzo":       None,
            "prezzo_pieno": None,
            "km":           None,
            "anno":         "",
            "data_immatricolazione": "",
            "is_venduta":   False,
            "motivo":       "",
        })

    return listings


# =============================================================================
# SCRAPING DETTAGLI (PREZZO, KM, VENDUTA)
# =============================================================================

def scrape_dettagli(auto):
    """
    Fa scraping della pagina HTML del listing per estrarre:
    prezzo, km, anno e stato venduto.
    Modifica il dict 'auto' in-place.
    """
    r = richiesta(auto["link"])
    if r is None:
        auto["motivo"] = "pagina non raggiungibile"
        return
    controlla_blocco(r)
    if r.status_code != 200:
        auto["motivo"] = f"pagina non leggibile (errore {r.status_code})"
        return
    html = r.text

    # ── Controllo venduta ─────────────────────────────────────────────────
    # 1. Label dall'API (es. "Auto Venduta", "Non Disponibile")
    if SOLD_LABEL_PATTERNS.search(auto["label"]):
        auto["is_venduta"] = True

    # 2. Banner/testo HTML — solo nelle prime 8000 chars (header/hero, non footer)
    if SOLD_HTML_PATTERNS.search(html[:8000]):
        auto["is_venduta"] = True

    # ── Prezzo ────────────────────────────────────────────────────────────
    # Metodo 1 (prioritario): blocco HTML strutturato listing-detail-price
    #   old-price = prezzo pieno, main-price = prezzo scontato finale
    price_block = re.search(
        r'class="listing-detail-price[^"]*">(.*?)(?=class="listing-detail-price|</section)',
        html, re.DOTALL
    )
    if price_block:
        m_old  = re.search(r'class="old-price">[^<]*<span class="price-text">([\d,\.]+)', price_block.group(1))
        m_main = re.search(r'class="main-price">[^<]*<span class="price-text">([\d,\.]+)', price_block.group(1))
        m_solo = re.search(r'class="price-text">([\d,\.]+)', price_block.group(1))
        if m_main:
            auto["prezzo_pieno"] = normalizza_prezzo(m_old.group(1) if m_old else m_main.group(1))
            auto["prezzo"]       = normalizza_prezzo(m_main.group(1))
        elif m_solo:
            v = normalizza_prezzo(m_solo.group(1))
            auto["prezzo_pieno"] = v
            auto["prezzo"]       = v

    # Metodo 2 (fallback testo promo): "Da X€ a Y€"
    if not auto["prezzo"]:
        match_da_a = re.search(r"Da\s*([\d\.,]+)\s*€\s*a\s*([\d\.,]+)\s*€", html, re.IGNORECASE)
        if match_da_a:
            auto["prezzo_pieno"] = normalizza_prezzo(match_da_a.group(1))
            auto["prezzo"]       = normalizza_prezzo(match_da_a.group(2))

    # Metodo 3 (fallback): "Valore commerciale X€"
    if not auto["prezzo"]:
        match_comm = re.search(r"Valore commerciale\s*([\d\.,]+)\s*€", html, re.IGNORECASE)
        if match_comm:
            v = normalizza_prezzo(match_comm.group(1))
            auto["prezzo_pieno"] = v
            auto["prezzo"]       = v

    # Metodo 4 (ultimo fallback): primo numero plausibile vicino a €
    if not auto["prezzo"]:
        match_gen = re.search(r"([\d]{1,2}\.[\d]{3}(?:,\d{2})?)\s*€", html)
        if match_gen:
            auto["prezzo"] = normalizza_prezzo(match_gen.group(1))

    # ── KM ────────────────────────────────────────────────────────────────
    # Cerca il primo valore km plausibile (> 1.000, < 500.000)
    km_matches = re.findall(r"([\d]{2,3}[.,][\d]{3})\s*(?:km|Km|KM)", html)
    for km_str in km_matches:
        km_val = normalizza_km(km_str)
        if km_val and 1000 <= km_val <= 500000:
            auto["km"] = km_val
            break

    # ── Anno + data immatricolazione ──────────────────────────────────────
    auto["anno"]                  = estrai_anno(auto["slug"], html)
    auto["data_immatricolazione"] = estrai_data_immatricolazione(html)

    # ── Dati obbligatori ──────────────────────────────────────────────────
    mancanti = [nome for nome, v in (("prezzo", auto["prezzo"]), ("km", auto["km"])) if not v]
    if mancanti:
        auto["motivo"] = "manca " + " e ".join(mancanti)


# =============================================================================
# FILTRO AUTO DISPONIBILI
# =============================================================================

def filtra_disponibili(listings):
    """Divide le auto in disponibili, escluse (con motivo) e vendute. Solo conteggi a video."""
    vendute     = [a for a in listings if a["is_venduta"]]
    escluse     = [a for a in listings if not a["is_venduta"] and a["motivo"]]
    disponibili = [a for a in listings if not a["is_venduta"] and not a["motivo"]]

    print(f"\n📊 Risultato scraping:")
    print(f"   ✅ Disponibili: {len(disponibili)}")
    print(f"   ⚠️  Escluse: {len(escluse)}")
    print(f"   ❌ Vendute: {len(vendute)}")

    return disponibili, escluse, vendute


def controlla_numeri(listings, disponibili, escluse, vendute):
    """Controlli prima di scrivere: se uno fallisce non esce nessun file."""
    non_vendute = len(listings) - len(vendute)
    if not disponibili:
        blocca("0 auto disponibili")
    if len(disponibili) + len(escluse) != non_vendute:
        blocca("auto nel feed + escluse diverse dalle auto non vendute")
    if len(escluse) / non_vendute > MAX_ESCLUSE:
        blocca(f"escluse {len(escluse)} auto su {non_vendute}, oltre il limite")


def scrivi_esclusi(escluse, output_dir):
    """Scrive esclusi.txt: una riga per auto, motivo e link."""
    path = os.path.join(output_dir, "esclusi.txt")
    with open(path, "w", encoding="utf-8") as f:
        f.write("# Auto non vendute rimaste fuori dal feed: motivo | link\n")
        for a in escluse:
            f.write(f"{a['motivo']} | {a['link']}\n")
    return path


# =============================================================================
# GENERAZIONE FEED GOOGLE VEHICLE ADS
# =============================================================================

def genera_feed_google(autos, output_dir):
    """
    Genera feed XML nel formato Google Vehicle Ads (Merchant Center).
    Spec: https://support.google.com/merchants/answer/7562221
    """
    path = os.path.join(output_dir, "feed_auto_google.xml")
    now  = datetime.now().strftime("%a, %d %b %Y %H:%M:%S +0000")

    # Namespace Google
    NS = "http://base.google.com/ns/1.0"

    rss = Element("rss", {
        "version": "2.0",
        "xmlns:g": NS,
    })
    channel = SubElement(rss, "channel")

    SubElement(channel, "title").text       = STORE_NAME
    SubElement(channel, "link").text        = STORE_URL
    SubElement(channel, "description").text = f"Feed auto usate — {STORE_NAME}"
    SubElement(channel, "lastBuildDate").text = now

    for a in autos:
        item = SubElement(channel, "item")

        def g(tag, text):
            if text is None or str(text).strip() == "":
                return
            el = SubElement(item, f"g:{tag}")
            el.text = str(text)

        # Titolo e link
        SubElement(item, "title").text       = a["title"]
        SubElement(item, "link").text        = a["link"]
        SubElement(item, "description").text = (
            f"{a['marca']} {a['title']} — Auto usata certificata. "
            f"Garanzia 12 mesi inclusa. {a['carburante']}, {a['cambio']}."
        )

        g("id",          a["id"])
        g("store_code",  STORE_CODE)
        g("link_template", a["link"] + "?store={store_code}&utm_source=google&utm_medium=vehicle_ads")
        g("condition",   CONDITION)
        g("availability", "in stock")
        vf = SubElement(item, "g:vehicle_fulfillment")
        SubElement(vf, "g:option").text     = "in_store"
        SubElement(vf, "g:store_code").text = STORE_CODE
        g("google_product_category", GOOGLE_CATEGORY)
        g("image_link",  a["foto_url"])

        # Prezzo: formato "6980.00 EUR"
        if a["prezzo"]:
            g("price", f"{a['prezzo']:.2f} {CURRENCY}")
        if a["prezzo_pieno"] and a["prezzo_pieno"] != a["prezzo"]:
            g("sale_price", f"{a['prezzo']:.2f} {CURRENCY}")

        # Veicolo
        g("brand",        a["marca"])
        g("make",         a["marca"])
        g("model",        a["title"].replace(a["marca"], "").strip() if a["marca"] else a["title"])
        g("year",         a["anno"])
        g("date_first_registered", a["data_immatricolazione"])
        g("mileage",      f"{a['km']} km" if a["km"] else "")
        g("body_style",   traduci_o_log(a["tipo"],        BODY_STYLE_MAP,   "body_style",   a["id"]))
        g("fuel_type",    traduci_o_log(a["carburante"],  FUEL_MAP,         "fuel_type",    a["id"]))
        g("transmission", traduci_o_log(a["cambio"],      TRANSMISSION_MAP, "transmission", a["id"]))
        g("color",        a["colore"])
        # g:vehicle_type rimosso — non esiste nella spec Google Vehicle Ads
        g("item_group_id", a["marca"].lower().replace(" ", "_") if a["marca"] else "auto")

    tree = ElementTree(rss)
    indent(tree, space="  ")
    with open(path, "wb") as f:
        f.write(b'<?xml version="1.0" encoding="UTF-8"?>\n')
        tree.write(f, encoding="utf-8", xml_declaration=False)

    return path


# =============================================================================
# GENERAZIONE FEED META AUTOMOTIVE INVENTORY ADS
# =============================================================================

def genera_feed_facebook(autos, output_dir):
    """
    Genera feed XML nel formato Meta Automotive Inventory Ads.
    Spec: https://www.facebook.com/business/help/1745533345568450
    """
    path = os.path.join(output_dir, "feed_auto_facebook.xml")
    now  = datetime.now().strftime("%a, %d %b %Y %H:%M:%S +0000")

    rss = Element("rss", {
        "version": "2.0",
        "xmlns:auto": "http://www.facebook.com/automotive/1.0",
    })
    channel = SubElement(rss, "channel")

    SubElement(channel, "title").text        = STORE_NAME
    SubElement(channel, "link").text         = STORE_URL
    SubElement(channel, "description").text  = f"Feed auto usate — {STORE_NAME}"
    SubElement(channel, "lastBuildDate").text = now

    for a in autos:
        item = SubElement(channel, "item")

        def t(tag, text):
            SubElement(item, tag).text = str(text) if text is not None else ""

        def auto_tag(tag, text):
            el = SubElement(item, f"auto:{tag}")
            el.text = str(text) if text is not None else ""

        t("id",           a["id"])
        t("title",        a["title"])
        t("link",         a["link"])
        t("description",  (
            f"{a['marca']} {a['title']} — Auto usata certificata. "
            f"Garanzia 12 mesi inclusa. {a['carburante']}, {a['cambio']}."
        ))
        t("image_link",   a["foto_url"])

        # Prezzo: formato "6980 EUR"
        if a["prezzo"]:
            t("price", f"{int(a['prezzo'])} {CURRENCY}")

        t("availability", "in stock")
        t("condition",    CONDITION)

        # Campi auto:
        auto_tag("make",         a["marca"])
        auto_tag("model",        a["title"].replace(a["marca"], "").strip() if a["marca"] else a["title"])
        auto_tag("year",         a["anno"])
        auto_tag("body_style",   a["tipo"])
        auto_tag("fuel_type",    a["carburante"])
        auto_tag("transmission", a["cambio"])
        auto_tag("drivetrain",   a["trazione"])
        auto_tag("color",        a["colore"])
        auto_tag("state_of_vehicle", "used")
        auto_tag("dealer_name",  STORE_NAME)
        auto_tag("dealer_phone", "+390248954311")

        # Chilometraggio come elemento strutturato
        if a["km"]:
            mileage_el = SubElement(item, "auto:mileage")
            SubElement(mileage_el, "auto:value").text = str(a["km"])
            SubElement(mileage_el, "auto:unit").text  = "KM"

    tree = ElementTree(rss)
    indent(tree, space="  ")
    with open(path, "wb") as f:
        f.write(b'<?xml version="1.0" encoding="UTF-8"?>\n')
        tree.write(f, encoding="utf-8", xml_declaration=False)

    return path


# =============================================================================
# MAIN
# =============================================================================

def main():
    print("=" * 60)
    print(f"  GENERA FEED AUTO — {STORE_NAME}")
    print(f"  {datetime.now().strftime('%d/%m/%Y %H:%M')}")
    print("=" * 60)

    # 1. Leggi listings da API
    listings = leggi_listings_api()

    # 2. Scraping prezzo, km, stato per ogni auto
    print(f"\n🔍 Scraping dettagli ({len(listings)} auto, pausa {PAUSA_SEC}s)...")
    for i, auto in enumerate(listings, 1):
        scrape_dettagli(auto)
        if i < len(listings):
            time.sleep(PAUSA_SEC)

    # 3. Filtra auto disponibili e controlla i numeri
    disponibili, escluse, vendute = filtra_disponibili(listings)
    controlla_numeri(listings, disponibili, escluse, vendute)

    # 4. Genera i feed in una cartella temporanea e li ricontrolla
    temp_dir = os.path.join(OUTPUT_DIR, ".feed_temp")
    os.makedirs(temp_dir, exist_ok=True)
    path_google = genera_feed_google(disponibili, temp_dir)
    path_fb     = genera_feed_facebook(disponibili, temp_dir)
    for path in (path_google, path_fb):
        if len(parse(path).findall("./channel/item")) != len(disponibili):
            blocca("il file generato non contiene tutte le auto")

    # 5. Solo ora sostituisce i file veri
    for path in (path_google, path_fb):
        os.replace(path, os.path.join(OUTPUT_DIR, os.path.basename(path)))
    os.rmdir(temp_dir)
    scrivi_esclusi(escluse, OUTPUT_DIR)

    # 6. Riepilogo finale
    print("\n" + "=" * 60)
    print(f"  COMPLETATO")
    print(f"  Auto nel feed: {len(disponibili)}")
    print(f"  Auto escluse:  {len(escluse)}")
    print(f"  Auto vendute:  {len(vendute)}")
    print("=" * 60)


if __name__ == "__main__":
    main()
