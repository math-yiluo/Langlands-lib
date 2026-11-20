# Gluing input from local data that agree on overlaps

Helper module for Zariski gluing (Task 7812). It turns the data of the sheaf
condition, data `a i` on the members `U i` of an open cover whose restrictions to
`U i ⊓ U j` are isomorphic, into the input of the gluing construction on small opens.

## Declarations

Namespace `Langlands.AbelianScheme.PolarizedFiniteLevel`:

- `Isomorphic.refl'`, `Isomorphic.symm'`, `Isomorphic.trans'`: `Isomorphic` is an
  equivalence relation (via `PolarizedIso.refl/symm/trans`).
- `Isomorphic.pullback'`: isomorphic data have isomorphic pullbacks.
- `Isomorphic.pullback_comp`: `a.pullback (f' ≫ f)` is isomorphic to
  `(a.pullback f).pullback f'` (`Datum.pullbackCompIso`).
- `Isomorphic.pullback_congr`: pullbacks along equal maps are isomorphic.

Namespace `...ZariskiGluing`, for `a : ∀ i, Datum P (U i) g d n`:

- `index W`, `le_index W`: a chosen member `U (index W)` containing the small open `W`.
- `localDatum a W := (a (index W)).pullback (S.homOfLE (le_index W))`.
- `isomorphic_restrict h V hi hj`: given the overlap hypothesis `h`, for `V ≤ U i` and
  `V ≤ U j` the restrictions of `a i` and `a j` to `V` are isomorphic (factor through
  `U i ⊓ U j`).
- `isomorphic_localDatum h W W' hWW'`: `localDatum a W` is isomorphic to the pullback of
  `localDatum a W'` along `W ≤ W'`.
- `transition h W W' hWW'`: a chosen polarized isomorphism realizing it
  (`Classical.choice`).

## Provenance

Internal bookkeeping.
