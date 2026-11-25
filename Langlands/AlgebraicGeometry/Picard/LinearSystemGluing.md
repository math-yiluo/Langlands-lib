# Gluing universal families of linear systems over an open cover of the base

Helper module of the proof of `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemStatement` (entry module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof`). It contains no `sorry` and no new axioms.

## Content

Namespace `Langlands.AlgebraicGeometry.Picard.LinearSystemGluing`.

- `isOpenImmersion_mapX`, `range_mapX`.
- `LocalData g m W`: for an open cover `W i` of `S`, schemes `P i`, maps `l i : P i ⟶ S`, ideal
  sheaves `D i`, with `P i` locally noetherian and `IsUniversalOn g m (W i) (l i) (D i)`.
- For a `LocalData` `A` and the basis cover of `S` by all opens contained in some `W i` (the
  Library's `SmoothFamilyOpenCover.basisCover`, which is locally directed): `param V` (the preimage
  of `V` in the chosen `P (idx V)`), `lp`, `Dp`, `universal_param`, `range_lp`; the transition
  maps `transition` for `V ≤ V'`, characterized by universality (`transition_lp`, `transition_D`,
  `transition_unique`, `transition_id`, `transition_comp`); the diagram `functor`, the
  transformation `natTrans` to the cover, and `equifibered` (each transition square is a pullback,
  by `isIso_of_isUniversalOn`); the Mathlib relative gluing datum `gluingData`, the glued scheme
  `glued` with `lG : glued ⟶ S`, the inclusions `ιV` and `ιV_lG`, `transition_ιV`, `range_ιV`,
  `mem_range_ιV`.

The construction follows the Library's `Picard/SmoothFamilyOpenCoverGluing`, with the linear-system
universality in place of rigidified families.

## Source

Kleiman (*The Picard scheme*, Theorem 3.13) works with the global module `Q` of EGA III 7.7.6 on a
general base. Here `Q` is only constructed over affine noetherian bases, so the representing schemes
over the affine opens are glued instead. Being universal over overlapping opens, they are unique up
to unique isomorphism there, which gives the gluing datum; the gluing itself is Mathlib's relative
gluing (`Scheme.Cover.RelativeGluingData`, Stacks Project, Tag 01LH).
