# Cartesian domains for prospective actions

Author: Worker 706.

This internal helper derives base change descriptions from scheme fibre
product universal properties. The intended application is the action descent
step in Stacks Project Proposition 70.8.1, Tag 07SU, registered as
`stacks-noetherian-approximation-2026-11-01`. The helper supplies domain
identifications; it does not construct an approximation system or descend a
map. All schemes have the same arbitrary universe `u`.

Fix a cartesian relation morphism from `E` to `F`, with object map `f` and
arrow map `g`. Supply an object pullback square with top map `k : P → Q`,
left map `p : P → E.U`, right map `q : Q → F.U`, and bottom map `f`.
No action map on either object is required.

`isPullback_arrowMap_fst` proves that the induced map between
`E.R ×[E.U] P` and `F.R ×[F.U] Q` is cartesian over the original arrow
map `g`, using the first fibre product projections. In the uniqueness
argument, the original arrow is fixed, and the two projections of the
supplied object pullback determine its source point. For existence, the
lower source point and the source of the supplied upper arrow lift to `P`;
pairing that lift with the upper arrow gives the required upper input.

Pasting this square with the original relation's target pullback proves
`isPullback_arrowMap_target`. Thus the upper action-arrow domain is the
base change of the lower domain along `f`, when each domain maps to its
base object by the target of its original arrow.
`arrowDomainTargetIso` is the canonical isomorphism with that fibre
product. Its `hom_fst` and `hom_snd` lemmas identify the comparison and
target projections.

`composableMap_eq_arrowMap` identifies the map on universal composable
inputs with the iterated arrow-domain map, taking the inner arrow's
target as the point's structural map. The proof compares the outer arrow,
inner arrow, and source-point projections. Applying the first pullback
result to the action-arrow target square gives
`isPullback_composableMap_outerArrow`. Pasting once more with the
original target square gives `isPullback_composableMap_target`.
`composableDomainTargetIso` identifies the upper composable-input domain
with the corresponding base change over the outer target; its two
`hom_fst` and `hom_snd` lemmas identify the comparison and target maps.
