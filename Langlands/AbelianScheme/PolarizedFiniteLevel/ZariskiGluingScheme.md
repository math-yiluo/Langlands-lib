# Gluing the underlying schemes of rigid data along the cover by small opens

Helper module for Zariski gluing of ordinary polarized full-level data (Task 7812).

## Setting

`hU : iSup U = ⊤` for an open cover `U` of `S`. Data `c W : Datum P W g d n` are given
on the opens `W : SubOpens U` (those below some member of `U`), each rigid (`hrig`:
every polarized automorphism of `c W` is the identity). For `W ≤ W'` there are
polarized isomorphisms
`θ W W' h : PolarizedIso (c W) ((c W').pullback (S.homOfLE h))`; nothing else is
assumed about them.

## Declarations

Namespace `Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing`.

- `gluingFunctor hU c hrig θ : (subCover hU).I₀ ⥤ Scheme`: sends `W` to the underlying
  scheme of `(c W).abelian` and `W ≤ W'` to `(θ W W' h).overMap`. Its functor laws are
  `PolarizedIso.overMap_eq_id` and `PolarizedIso.overMap_comp` (rigidity), with
  `Scheme.homOfLE_rfl` and `Scheme.homOfLE_homOfLE`.
- `gluingNatTrans`: the structure maps `(c W).abelian.X.hom`, natural by
  `PolarizedIso.overMap_w` and `subCover_trans`.
- `gluingData : (subCover hU).RelativeGluingData`: equifibered by
  `PolarizedIso.isPullback_overMap`.
- `gluingData_isPullback W`: the piece `(c W).abelian.X.left` is the preimage of `W` in
  the glued scheme, i.e. the square with `colimit.ι`, `W.ι` and the glued structure map
  `toBase` is cartesian (Mathlib's `isPullback_natTrans_ι_toBase`).

## Provenance

Relative gluing of schemes over a base along a locally directed open cover: Stacks
Project Tag 01LH, as formalized in Mathlib (`AlgebraicGeometry.RelativeGluing`). The
use of rigidity to make transition maps functorial is internal.
