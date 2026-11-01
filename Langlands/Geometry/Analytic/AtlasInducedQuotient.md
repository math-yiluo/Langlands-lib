# Full bounded maps between induced balanced-quotient atlases

Author: Worker 56. Namespace: `Langlands.Analytic.AtlasInducedAction`.

This internal construction transports the existing coset-copy induction maps
to the actual balanced quotient. Let `K : Type u` be a complete normed
ultrametric field, `G : Type z` a topological group, and `H` an open subgroup.
The supplied categorical subgroup actions `X`, `Y` and `Z` lie in
`AffinoidAtlasPresentation.{u, max z v, max z w} K`. Each action used to form
a quotient has `ContinuousSMul H (LocalSpace H X)` for its specific point
action obtained from its complete action arrows. No topology on analytic
automorphisms is assumed or constructed here.

For every original complete equivariant arrow `f : X ⟶ Y`, `quotientMap`
is the composite of the inverse source copies isomorphism, `copiesMap H f`,
and the target copies isomorphism. These are constructed bounded arrows.
`copiesIso_quotientMap` proves the complete transport square. The composite
of the corresponding equivariant isomorphisms and `copiesEquivariantMap`
proves whole-arrow equivariance, which `quotientEquivariantMap` bundles.
The previously proved identity and composition laws for `copiesMap` and
cancellation of the actual transport isomorphisms prove identity and
composition for the quotient maps.

The normalized unit is natural for these whole arrows: substitute the
transported maps, cancel the intermediate copies isomorphism, and use the
existing complete unit naturality. The target chart index is the coset tag
together with the original normalized chosen index of `f`. Both transport
arrows have bounded identity pullbacks, so their cancellation leaves exactly
the original `f.hom.pullback i.val` on every surviving original chart.

At the unit, evaluating complete naturality and using the existing exact
unit realization gives `[1,x] ↦ [1,f(x)]`. Every representative satisfies
`[g,x] = g • [1,x]`. Evaluating the complete quotient equivariance equation,
then the exact quotient action realization and the unit equation, proves
`quotientMap_mk`: the actual point map is `[g,x] ↦ [g,f(x)]` for every
`g ∈ G` and source point `x`.

The provenance is internal transport of the constructed arbitrary-atlas
induction functor and normalized unit. No quotient morphism, equivariance,
functor law or representative formula is supplied as an input. All
bounded-arrow equalities are proved categorically before point evaluation;
pointwise agreement is never used to identify bounded algebra maps.
Original chart overlaps and restrictions are retained by the existing
copies isomorphisms, with empty charts removed by the same-space
normalization. Empty spaces and chart-index types and infinite index of
`H` are allowed. The source of the unit remains that normalization.
Arbitrary-target quotient extension, a bundled functor on continuous input
actions, the explicit nonempty-chart adjunction, analytic automorphism
continuity, refinement localization, general analytic sites and Harris
tower specialization remain separate obligations.
