# Recovering a relation from an open part and a trivial complement

This is an internal categorical helper for the pushout step of Stacks
Proposition 70.8.1 (Tag 07SU), registered in
`stacks-noetherian-approximation-2026-11-01`. Its proof is derived from the
actual open-extension pushout, cartesian relation morphisms, and Mathlib's
scheme pullback and flat-monomorphism results.

Let `E → F` be a cartesian morphism of étale equivalence relations whose object
map `f` is an open immersion. `toOriginal` constructs the canonical map from the
open extension of `E` along `f` to the original arrow scheme `F.R`.
`unit_toOriginal` and `inclusion_toOriginal` give the chart equations;
`toOriginal_t` and `toOriginal_s` give its endpoint equations.

`mono_toOriginal` follows from endpoint uniqueness for the extension.
`isOpenImmersion_old` follows from the original source pullback.
`etale_toOriginal` checks étaleness on the two source charts, and
`isOpenImmersion_toOriginal` applies the theorem that a flat monomorphism locally
of finite presentation is an open immersion.
`surjective_of_cover` and `isIso_of_cover` show that coverage of `F.R` by the
old arrow chart and the unit chart makes the canonical map an isomorphism.

For the complement criterion, let `d : D → F.U` have image containing every
point outside the image of `f`. Suppose the source pullback along `d` is
the identity relation on `D`: its two maps are `d ≫ F.unit` and `𝟙 D`.
`cover_of_complement` proves arrow coverage by splitting according to whether
an arrow's source lies in the old open. Existence of points in scheme
pullbacks supplies an old arrow in the first case and a unit in the second.
No factorization through a reduced closed subscheme is used.

`isIso_of_complement` applies the coverage criterion, and `arrowsIso` is the
resulting actual isomorphism of arrow schemes. `arrowsIso_hom` identifies its
forward map; `arrowsIso_inv_t` and `arrowsIso_inv_s` identify its inverse's
endpoint composites. `isCartesianHom` gives the recovery morphism with identity
map on object schemes.

All schemes lie in an arbitrary universe `u`. The helper assumes no affineness,
Noetherianity, or separation, and does not construct a Noetherian first level.
