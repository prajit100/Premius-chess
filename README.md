# Premium Canvas Chess (Offline)

A production-quality, single-player **Human vs AI** chess game that runs entirely in the browser and renders using **HTML5 Canvas** (no external chessboard UI libraries).

## Features
- Full legal chess rules: castling, en passant, promotion, check/checkmate/stalemate
- Draw detection: threefold repetition, 50‑move rule, insufficient material
- Smooth animations, responsive layout, touch + mouse support
- Modern UI: move list (SAN), captured pieces, status indicators
- Strong AI: minimax with alpha‑beta pruning, iterative deepening, time limits, transposition table (Zobrist hashing)
- Difficulty levels: Easy / Medium / Hard / Expert

## Run locally
### Option A: Open directly
Just open `index.html` in a modern browser (Chrome/Edge/Firefox/Safari).

### Option B: Local server (recommended)
Some browsers restrict certain features when opening local files. A simple local server is safest:

**Python**
```bash
python -m http.server 8000
```
Then open `http://localhost:8000`.

## Files
- `index.html` – UI structure
- `styles.css` – modern styling
- `main.js` – all game logic (rules, AI, rendering, UI)
- `assets/` – reserved if you want to add sprites (this project draws pieces on canvas)

## Notes
- Ranked mode disables Undo.
- The AI uses iterative deepening with a time cap per move. Expert is strongest and uses the largest time cap.
