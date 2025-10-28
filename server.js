import express from 'express';
import multer from 'multer';
import fs from 'fs';
import { PDFDocument, StandardFonts, rgb } from 'pdf-lib';
import path from 'path';
import { PDFParse } from 'pdf-parse';

// Extract per-page blocks between header and footer and find Karteninhaber per page
function extractPerPageBlocks(fullText) {
  const pageSplitRegex = /--\s*\d+\s+of\s+\d+\s*--/i;
  let rawPages = fullText.split(pageSplitRegex).map(p => p.trim()).filter(p => p.length > 0);
  if (rawPages.length === 0) rawPages = fullText.split('\f').map(p => p.trim()).filter(p => p.length > 0);
  if (rawPages.length === 0) rawPages = [fullText];

  const results = [];
  for (let pi = 0; pi < rawPages.length; pi++) {
    const pageText = rawPages[pi];
    const lines = pageText.split(/\r?\n/).map(l => l.trim()).filter(l => l.length > 0);

    const headerIdx = lines.findIndex(l => /Fremdwährung\s+Kurs\s+FW\s+Betrag\s+in\s+EUR/i.test(l));
  const footerIdx = lines.findIndex(l => /(?:Zwischensaldo|Aktueller Saldo)/i.test(l));

    let blockLines = [];
    if (headerIdx !== -1 && footerIdx !== -1 && footerIdx > headerIdx) {
      blockLines = lines.slice(headerIdx + 1, footerIdx);
    } else if (headerIdx !== -1) {
      blockLines = lines.slice(headerIdx + 1);
    }

    // find Karteninhaber on this page: look for 'Karteninhaber' or 'Kontoinhaber' or name-like line
    let holder = null;
    // Unicode-aware regex for name capture (allow letters including umlauts and ß)
    for (let k = 0; k < Math.min(8, lines.length); k++) {
      const l = lines[k];
      const kontRegex = /Karteninhaber[:\s\-]*([\p{L}\p{M}0-9\s\.,\-]+)/iu;
      const kontMatch = kontRegex.exec(l);
      if (kontMatch) { holder = kontMatch[1].trim(); break; }
      const kont2 = /Kontoinhaber[:\s\-]*([\p{L}\p{M}0-9\s\.,\-]+)/iu.exec(l);
      if (kont2) { holder = kont2[1].trim(); break; }
    }
    if (!holder) {
      // broader Unicode-aware name detection
      const nameLine = lines.find(l => /^[\p{Lu}][\p{L}\p{M}0-9\.\- ]+$/u.test(l) && (l.replace(/[^0-9]/g, '').length < 3));
      if (nameLine) holder = nameLine;
    }
    if (!holder) holder = `Page-${pi+1}-UNKNOWN`;

    results.push({ page: pi + 1, name: holder, lines: blockLines });
  }
  return results;
}

// Helper: parse German formatted number strings to float
function parseGermanNumberToFloat(s) {
  if (!s || typeof s !== 'string') return null;
  let t = s.replace(/\s+/g, '');
  if (t.indexOf('.') !== -1 && t.indexOf(',') !== -1) {
    t = t.replace(/\./g, '').replace(/,/g, '.');
  } else if (t.indexOf(',') !== -1 && t.indexOf('.') === -1) {
    t = t.replace(/,/g, '.');
  } else {
    t = t.replace(/\./g, '');
  }
  t = t.replace(/[^0-9.\-+]/g, '');
  const n = parseFloat(t);
  return isNaN(n) ? null : n;
}

// Helper: parse a raw line into structured entry
function parseLineToEntry(raw) {
  const entry = { raw };
  const dateRegex = /\b(\d{1,4}[\.\-/]\d{1,2}[\.\-/]\d{1,4})\b/g;
  const dates = [];
  let m;
  while ((m = dateRegex.exec(raw)) !== null) dates.push(m[1]);
  entry.umsatzVom = dates[0] || null;
  entry.buchungAm = dates[1] || null;

  // amount patterns
  let amountStr = null;
  let sign = null;
  let amountVal = null;

  const trailingSignRegex = /([0-9]{1,3}(?:[\.,][0-9]{3})*(?:[\.,][0-9]{2}))\s*([+-])\s*$/;
  const trailingMatch = raw.match(trailingSignRegex);
  if (trailingMatch) {
    amountStr = trailingMatch[1];
    sign = trailingMatch[2];
    amountVal = parseGermanNumberToFloat(amountStr);
  } else {
    const altRegex = /([+-])?\s*([0-9]{1,3}(?:[\.,][0-9]{3})*(?:[\.,][0-9]{2}))\s*[€EUR]*$/i;
    const altMatch = raw.match(altRegex);
    if (altMatch) {
      sign = altMatch[1] || null;
      amountStr = altMatch[2];
      amountVal = parseGermanNumberToFloat(amountStr);
    }
  }

  entry.amountStr = amountStr;
  entry.sign = sign;
  entry.amount = amountVal;

  // detect foreign currency blocks like: USD 125,00 1,15456 (optional sign after foreign amount)
  const fxRegex = /\b([A-Z]{3})\W*([0-9]{1,3}(?:[\.,][0-9]{3})*(?:[\.,][0-9]{2}))(?:\s*([-+]))?\W+([0-9]+(?:[\.,][0-9]+))\b/i;
  const fxMatch = raw.match(fxRegex);
  if (fxMatch) {
    entry.foreignCurrency = fxMatch[1];
    entry.foreignAmountStr = fxMatch[2];
    entry.foreignSign = fxMatch[3] || null;
    entry.foreignAmount = parseGermanNumberToFloat(entry.foreignAmountStr);
    entry.fxRateStr = fxMatch[4];
    entry.fxRate = parseGermanNumberToFloat(entry.fxRateStr);
  } else {
    entry.foreignCurrency = null;
    entry.foreignAmountStr = null;
    entry.foreignSign = null;
    entry.foreignAmount = null;
    entry.fxRateStr = null;
    entry.fxRate = null;
  }

  // Rechnungstext: remove dates, fx block, amount and sign from raw
  let text = raw;
  if (entry.umsatzVom) text = text.replace(entry.umsatzVom, '');
  if (entry.buchungAm) text = text.replace(entry.buchungAm, '');
  if (fxMatch && fxMatch[0]) text = text.replace(fxMatch[0], '');
  if (amountStr) text = text.replace(amountStr, '');
  if (entry.sign) text = text.replace(entry.sign, '');
  text = text.replace(/\b(EUR|€)\b/ig, '').replace(/[\t\n\r]/g, ' ').replace(/\s{2,}/g, ' ').trim();
  entry.rechnungstext = text || null;
  return entry;
}

// Helper: build date string variants for matching (not stored in entries)
function buildDateVariants(dstr) {
  if (!dstr) return [];
  const parts = dstr.split(/[\.\-/]/).map(p => p.trim());
  if (parts.length !== 3) return [dstr.toLowerCase()];
  const [p1, p2, p3] = parts;
  const variants = new Set();
  // year first
  if (p1.length === 4) {
    variants.add(`${p1}.${p2.padStart(2, '0')}.${p3.padStart(2, '0')}`);
    variants.add(`${p1}-${p2.padStart(2, '0')}-${p3.padStart(2, '0')}`);
    variants.add(`${p3}.${p2}.${p1}`);
    variants.add(`${p2}.${p3}.${p1}`);
  } else if (p3.length === 4) {
  // dd.mm.yyyy and variants including month-name forms and slash variants
  variants.add(`${p1.padStart(2, '0')}.${p2.padStart(2, '0')}.${p3}`);
  variants.add(`${p2.padStart(2, '0')}.${p1.padStart(2, '0')}.${p3}`);
  // slash-separated forms: '01/01/2025' and '01/01/2025' (mm/dd and dd/mm depending on source)
  variants.add(`${p1.padStart(2, '0')}/${p2.padStart(2, '0')}/${p3}`);
  variants.add(`${p2.padStart(2, '0')}/${p1.padStart(2, '0')}/${p3}`);
    variants.add(`${p3}-${p2.padStart(2, '0')}-${p1.padStart(2, '0')}`);
    variants.add(`${p3}.${p2}.${p1}`);
    try {
      const monthNames = ['Jan','Feb','Mar','Apr','May','Jun','Jul','Aug','Sep','Oct','Nov','Dec'];
      const monthNamesFull = ['January','February','March','April','May','June','July','August','September','October','November','December'];
      const mi = parseInt(p2, 10) - 1;
      if (!isNaN(mi) && mi >= 0 && mi < 12) {
        const mn = monthNames[mi];
        const mnFull = monthNamesFull[mi];
        // Day before month: '31. Aug 2025', '31. Aug. 2025', '31 Aug 2025', '31. August 2025'
        variants.add(`${p1.padStart(2,'0')}. ${mn} ${p3}`);
        variants.add(`${p1.padStart(2,'0')}. ${mn}. ${p3}`);
        variants.add(`${p1.padStart(2,'0')} ${mn} ${p3}`);
        variants.add(`${p1.padStart(2,'0')}. ${mnFull} ${p3}`);
        variants.add(`${p1.padStart(2,'0')} ${mnFull} ${p3}`);
        // Month before day (US-style): 'Aug 27, 2025', 'Aug 27 2025', 'Aug. 27, 2025', and full month 'September 11, 2025'
        variants.add(`${mn} ${p1.padStart(2,'0')}, ${p3}`);
        variants.add(`${mn} ${p1.padStart(2,'0')} ${p3}`);
        variants.add(`${mn}. ${p1.padStart(2,'0')}, ${p3}`);
        variants.add(`${mn}. ${p1.padStart(2,'0')} ${p3}`);
        variants.add(`${mnFull} ${p1.padStart(2,'0')}, ${p3}`);
        variants.add(`${mnFull} ${p1.padStart(2,'0')} ${p3}`);
        variants.add(`${mnFull} ${p1.padStart(2,'0')}. ${p3}`);
      }
    } catch (e) {}
  } else {
    variants.add(dstr);
  }
  return Array.from(variants).map(s => s.toLowerCase());
}

const app = express();
const upload = multer({ dest: 'uploads/' });
app.use(express.static('public'));

// Analyze endpoint: return parsed per-page report JSON for a given main PDF
app.post('/analyze', upload.single('main'), async (req, res) => {
  const file = req.file;
  if (!file) return res.status(400).json({ error: 'Main PDF (field name "main") is required' });
  try {
    const filePath = path.resolve(file.path);
    const bytes = fs.readFileSync(filePath);
    const parsed = await (await new PDFParse({ data: bytes })).getText();
    const fullText = parsed && parsed.text ? parsed.text : '';
    const perPage = extractPerPageBlocks(fullText);

    const skipRegex = /Übertrag auf Rechnungsübersicht|Übertrag/i;
    const reported = perPage.slice(2).map(p => {
      let entries = (p.lines || []).map(l => parseLineToEntry(l));
      entries = entries.filter(e => {
        const hay = (e.rechnungstext || e.raw || '');
        // skip summary lines and entries explicitly labeled as MANIPULATIONSENTGELT
        if (skipRegex.test(hay)) return false;
        const rt = (e.rechnungstext || '').toString().trim().toLowerCase();
        if (rt === 'manipulationsentgelt') return false;
        return true;
      });
      return { page: p.page, name: p.name, entries };
    });

    const report = { detectedPages: perPage.length, reportedPages: reported.length, pages: reported };
    // cleanup uploaded main file
    try { fs.unlinkSync(filePath); } catch (e) {}
    return res.json(report);
  } catch (e) {
    return res.status(500).json({ error: e.message });
  }
});

app.post('/combine', upload.any(), async (req, res) => {
  // multer.any() populates req.files as an array; pick out the main file by fieldname
  const files = Array.isArray(req.files) ? req.files : [];
  const mainFiles = files.filter(f => f.fieldname === 'main');
  const otherFiles = files.filter(f => f.fieldname !== 'main');
  if (mainFiles.length === 0) return res.status(400).json({ error: 'Main PDF (field name "main") is required' });

  try {
  const mergedPdf = await PDFDocument.create();
  // merged page tracking and missing placeholder collection (outer scope so response can reference)
  let mergedPageCount = 0;
  const missingPlaceholders = [];

    // Add original main PDF pages first
    const mainFile = mainFiles[0];
    const mainPath = path.resolve(mainFile.path);
    const mainBytes = fs.readFileSync(mainPath);
  const mainSrc = await PDFDocument.load(mainBytes);

    // Analyze main PDF per page and log the blocks
    try {
      const parser = new PDFParse({ data: mainBytes });
      const parsed = await parser.getText();
      const fullText = parsed.text || '';
      const perPage = extractPerPageBlocks(fullText);

      // helpers
      function parseGermanNumberToFloat(s) {
        if (!s || typeof s !== 'string') return null;
        let t = s.replace(/\s+/g, '');
        if (t.indexOf('.') !== -1 && t.indexOf(',') !== -1) {
          t = t.replace(/\./g, '').replace(/,/g, '.');
        } else if (t.indexOf(',') !== -1 && t.indexOf('.') === -1) {
          t = t.replace(/,/g, '.');
        } else {
          t = t.replace(/\./g, '');
        }
        t = t.replace(/[^0-9.\-+]/g, '');
        const n = parseFloat(t);
        return isNaN(n) ? null : n;
      }

      function parseLineToEntry(raw) {
        const entry = { raw };
        const dateRegex = /\b(\d{2}\.\d{2}\.\d{4})\b/g;
        const dates = [];
        let m;
        while ((m = dateRegex.exec(raw)) !== null) dates.push(m[1]);
        entry.umsatzVom = dates[0] || null;
        entry.buchungAm = dates[1] || null;

        // amount patterns: trailing sign (e.g. 1.234,56-), or amount at end with optional +/-, or sign before amount
        let amountStr = null;
        let sign = null;
        let amountVal = null;

        const trailingSignRegex = /([0-9]{1,3}(?:[\.,][0-9]{3})*(?:[\.,][0-9]{2}))[\s]*([+-])\s*$/;
        const trailingMatch = raw.match(trailingSignRegex);
        if (trailingMatch) {
          amountStr = trailingMatch[1];
          sign = trailingMatch[2];
          amountVal = parseGermanNumberToFloat(amountStr);
        } else {
          const altRegex = /([+-])?\s*([0-9]{1,3}(?:[\.,][0-9]{3})*(?:[\.,][0-9]{2}))[\s€EUR]*$/i;
          const altMatch = raw.match(altRegex);
          if (altMatch) {
            sign = altMatch[1] || null;
            amountStr = altMatch[2];
            amountVal = parseGermanNumberToFloat(amountStr);
          }
        }

        entry.amountStr = amountStr;
        entry.sign = sign;
        entry.amount = amountVal;

        // detect foreign currency blocks like: USD 125,00 1,15456
        // currency code (3 uppercase letters), foreign amount, fx rate
  // allow optional sign after foreign amount (e.g. 'USD 125,00- 1,15456')
  // be permissive: allow punctuation between currency code and amount, case-insensitive
  const fxRegex = /\b([A-Z]{3})\W*([0-9]{1,3}(?:[\.,][0-9]{3})*(?:[\.,][0-9]{2}))(?:\s*([-+]))?\W+([0-9]+(?:[\.,][0-9]+))\b/i;
        const fxMatch = raw.match(fxRegex);
        if (fxMatch) {
          entry.foreignCurrency = fxMatch[1];
          entry.foreignAmountStr = fxMatch[2];
          entry.foreignSign = fxMatch[3] || null;
          entry.foreignAmount = parseGermanNumberToFloat(entry.foreignAmountStr);
          entry.fxRateStr = fxMatch[4];
          entry.fxRate = parseGermanNumberToFloat(entry.fxRateStr);
        } else {
          entry.foreignCurrency = null;
          entry.foreignAmountStr = null;
          entry.foreignSign = null;
          entry.foreignAmount = null;
          entry.fxRateStr = null;
          entry.fxRate = null;
        }

        // Rechnungstext: remove dates, fx block, amount and sign from raw
        let text = raw;
        if (entry.umsatzVom) text = text.replace(entry.umsatzVom, '');
        if (entry.buchungAm) text = text.replace(entry.buchungAm, '');
        if (fxMatch && fxMatch[0]) text = text.replace(fxMatch[0], '');
        if (amountStr) text = text.replace(amountStr, '');
        if (entry.sign) text = text.replace(entry.sign, '');
        text = text.replace(/\b(EUR|€)\b/ig, '').replace(/[\t\n\r]/g, ' ').replace(/\s{2,}/g, ' ').trim();
        entry.rechnungstext = text || null;
        return entry;
      }

      // ignore the first two pages (indices 0 and 1)
      const skipRegex = /Übertrag auf Rechnungsübersicht|Übertrag/i;
      const reported = perPage.slice(2).map(p => {
        let entries = (p.lines || []).map(l => parseLineToEntry(l));
        entries = entries.filter(e => {
          const hay = (e.rechnungstext || e.raw || '');
          if (skipRegex.test(hay)) return false;
          const rt = (e.rechnungstext || '').toString().trim().toLowerCase();
          if (rt === 'manipulationsentgelt') return false;
          return true;
        });
        return { page: p.page, name: p.name, entries };
      });

      // output as a single JSON string to the console for easy parsing
      // console.log(JSON.stringify({ detectedPages: perPage.length, reportedPages: reported.length, pages: reported }, null, 2));

      // Preload uploaded PDFs and parse their text for matching
      const uploaded = [];
      for (const file of otherFiles) {
        try {
          const filePath = path.resolve(file.path);
          const bytes = fs.readFileSync(filePath);
          const parsed = await (async () => {
            try { const r = await (await new PDFParse({ data: bytes }).getText()); return r; } catch (e) { return { text: '' }; }
          })();
          uploaded.push({ file, bytes, text: (parsed && parsed.text) ? parsed.text.toLowerCase() : '', used: false });
        } catch (e) {
          // ignore unreadable uploaded files
        }
      }
      // Debug: log uploaded file summaries
      try {
        const uploadedSummary = uploaded.map(u => ({
          filename: u.file.filename,
          originalname: u.file.originalname,
          size: u.file.size,
          used: u.used,
          textSnippet: (u.text || '').slice(0, 200).replace(/\s+/g, ' ')
        }));
        console.log('Uploaded summaries for matching:', JSON.stringify(uploadedSummary, null, 2));
      } catch (e) { /* ignore */ }

  const helvetica = await mergedPdf.embedFont(StandardFonts.Helvetica);
  const srcPages = mainSrc.getPages();

      function normalizeForMatch(s) {
        if (!s) return '';
        return s.toString().toLowerCase().replace(/[^\p{L}0-9,\.\-\s]/giu, ' ').replace(/\s{2,}/g, ' ').trim();
      }

      // for each original page, add it, then for each of its entries try to insert matching uploaded pdf or a blank page
      for (let i = 0; i < srcPages.length; i++) {
  const [copiedPage] = await mergedPdf.copyPages(mainSrc, [i]);
  mergedPdf.addPage(copiedPage);
  mergedPageCount += 1;

        const pageReport = reported.find(r => r.page === i + 1);
        if (!pageReport || !Array.isArray(pageReport.entries)) continue;

        for (const entry of pageReport.entries) {
          // try to find an unused uploaded PDF that matches this entry
          const entryText = normalizeForMatch(entry.rechnungstext || entry.raw || '');
          const entryAmountStr = (entry.amountStr || '').replace(/\./g, '').replace(/,/g, '.');
          const entryDate = (entry.umsatzVom || '').toString();
          const pageName = (pageReport && pageReport.name) ? pageReport.name.toString().toLowerCase() : '';
          // New matching rule: require exact presence of a date variant (if entry has a date)
          // and presence of the amount string (raw or normalized) in the uploaded PDF text.
          let matched = null;
          for (const u of uploaded) {
            if (u.used) continue;
            const ft = (u.text || '').toLowerCase();

            const esc = s => (s || '').toString().replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
            const dateVariants = [];
            if (entry.umsatzVom) dateVariants.push(...buildDateVariants(entry.umsatzVom));
            if (entry.buchungAm) dateVariants.push(...buildDateVariants(entry.buchungAm));
            let dateMatched = false;
            if (dateVariants.length === 0) dateMatched = true;
            else {
              for (const v of dateVariants) {
                const vEsc = esc(v);
                const dateRe = new RegExp('(^|[^0-9])' + vEsc + '($|[^0-9])');
                if (dateRe.test(ft)) { dateMatched = true; break; }
              }
            }

            let amountMatched = false;
            if (entry.foreignAmountStr) {
              const rawAmt = entry.foreignAmountStr.toString().toLowerCase();
              const normAmt = rawAmt.replace(/\./g, '').replace(/,/g, '.');
              const rawEsc = esc(rawAmt);
              const normEsc = esc(normAmt);
              const rawRe = new RegExp('(^|[^0-9\\\.,%])' + rawEsc + '($|[^0-9\\\.,%])');
              const normRe = new RegExp('(^|[^0-9\\\.,%])' + normEsc + '($|[^0-9\\\.,%])');
              if (rawRe.test(ft) || normRe.test(ft)) amountMatched = true;
            } else if (entry.amountStr) {
              const rawAmt = entry.amountStr.toString().toLowerCase();
              const normAmt = rawAmt.replace(/\./g, '').replace(/,/g, '.');
              const rawEsc = esc(rawAmt);
              const normEsc = esc(normAmt);
              const rawRe = new RegExp('(^|[^0-9\\\.,%])' + rawEsc + '($|[^0-9\\\.,%])');
              const normRe = new RegExp('(^|[^0-9\\\.,%])' + normEsc + '($|[^0-9\\\.,%])');
              if (rawRe.test(ft) || normRe.test(ft)) amountMatched = true;
            } else {
              amountMatched = true;
            }

            if (dateMatched && amountMatched) { matched = u; break; }
          }
          if (matched) matched.used = true;

          if (matched) {
            // add the whole PDF
            try {
              const src = await PDFDocument.load(matched.bytes);
              const copied = await mergedPdf.copyPages(src, src.getPageIndices());
              copied.forEach(p => mergedPdf.addPage(p));
              mergedPageCount += copied.length;
            } catch (e) {
              // if load fails, fall back to a blank page
              const np = mergedPdf.addPage([copiedPage.getWidth(), copiedPage.getHeight()]);
              np.drawText('(failed to attach matched PDF)', { x: 50, y: np.getHeight() - 50, size: 12, font: helvetica });
              mergedPageCount += 1;
            }
          } else {
            // create a blank page (or pages) with a red background and render the entry details on it
            const width = copiedPage.getWidth ? copiedPage.getWidth() : 595.28;
            const height = copiedPage.getHeight ? copiedPage.getHeight() : 841.89;
            const newPage = mergedPdf.addPage([width, height]);
            mergedPageCount += 1;
            const placeholderPages = [mergedPageCount];

            // fill background red
            try {
              newPage.drawRectangle({ x: 0, y: 0, width, height, color: rgb(0.85, 0.1, 0.1) });
            } catch (e) {
              // if rgb helper isn't available, fallback to a darker red by drawing multiple rectangles (older pdf-lib versions)
              try {
                newPage.drawRectangle({ x: 0, y: 0, width, height, color: { r: 0.85, g: 0.1, b: 0.1 } });
              } catch (e) { /* ignore */ }
            }

            // prepare lines to draw (same format as when we rendered entries earlier)
            const lines = [];
            lines.push(`Umsatz vom: ${entry.umsatzVom || ''}`);
            lines.push(`Buchung am: ${entry.buchungAm || ''}`);
            lines.push(`Rechnungstext: ${entry.rechnungstext || ''}`);
            if (entry.foreignCurrency) {
              lines.push(`Foreign: ${entry.foreignCurrency} ${entry.foreignAmountStr || ''} @ ${entry.fxRateStr || ''} ${entry.foreignSign || ''}`);
            }
            lines.push(`Amount: ${entry.amountStr || ''} ${entry.sign || ''}`);
            lines.push('--- Raw ---');
            lines.push(entry.raw || '');

            // wrapping logic
            const wrapped = [];
            for (const ln of lines) {
              if (!ln) continue;
              const maxChars = 90;
              if (ln.length <= maxChars) wrapped.push(ln);
              else {
                for (let pos = 0; pos < ln.length; pos += maxChars) wrapped.push(ln.slice(pos, pos + maxChars));
              }
            }

            const fontSize = 12;
            const margin = 50;
            let cursorY = height - margin;
            for (const wl of wrapped) {
              if (cursorY < margin + fontSize) {
                // start a new page if out of space
                const extraPage = mergedPdf.addPage([width, height]);
                mergedPageCount += 1;
                // fill background on extra page as well
                try { extraPage.drawRectangle({ x: 0, y: 0, width, height, color: rgb(0.85, 0.1, 0.1) }); } catch (e) {}
                cursorY = height - margin;
                extraPage.drawText(wl, { x: margin, y: cursorY, size: fontSize, font: helvetica, color: rgb(1,1,1) });
                placeholderPages.push(mergedPageCount);
                cursorY -= fontSize + 6;
              } else {
                newPage.drawText(wl, { x: margin, y: cursorY, size: fontSize, font: helvetica, color: rgb(1,1,1) });
                cursorY -= fontSize + 6;
              }
            }
            // record this missing placeholder entry (pages and expected entry data)
            missingPlaceholders.push({ pages: placeholderPages, expected: { originalPage: pageReport.page, owner: pageReport.name, entry } });
          }
        }
      }
    } catch (e) {
      console.warn('Failed to parse main PDF for per-page blocks:', e.message);
    }

    // NOTE: uploaded PDFs are inserted where matched to entries above.
    // Do not append all uploaded PDFs at the end — removed the previous append-all loop.

    const mergedBytes = await mergedPdf.save();

    // cleanup uploaded files (main + others)
    for (const f of files) {
      try { fs.unlinkSync(path.resolve(f.path)); } catch (e) { /* ignore */ }
    }

    // return JSON: base64 PDF and missing placeholders so the frontend can render it
    const b64 = Buffer.from(mergedBytes).toString('base64');
    res.json({ pdf: b64, missingPlaceholders });
  } catch (err) {
    console.error(err);
    res.status(500).json({ error: err.message });
  }
});

const PORT = process.env.PORT || 3000;
app.listen(PORT, () => {
  console.log(`Server listening on http://localhost:${PORT}`);
});
