# Full locally constant smooth equivariant sheaves

This internal construction proves that the full ordinary-open locally constant
module sheaf of a smooth coefficient representation is a smooth equivariant
sheaf. The commutative coefficient ring, coefficient module and space lie in
`Type u`, as required by the existing smooth-sheaf category. The group lies in
independent `Type v`. Its topology need not be discrete. The action has continuous
individual operators and satisfies `HasStableNeighbourhoods`: every open
neighborhood contains an open neighborhood stable under an open subgroup. No
topology on the coefficient module is used.

For a section `s` on an open `U` and a point `x` of `U`, its fiber through `s(x)`
is open in `U`, hence its image is open in the ambient space. Choose a stable
open neighborhood `V` of `x` inside this fiber. Smoothness of the coefficient
representation gives an open subgroup fixing `s(x)`. Intersect it with the open
subgroup stabilizing `V`. On `V` the section is constant, so inverse spatial
pullback followed by the coefficient action fixes the actual restriction of
`s`. This proves `isSmoothSheaf` for all original sections on all opens.

`smoothSheaf` bundles this unchanged sheaf and its proved smoothness.
`smoothFunctor` uses every original pointwise coefficient intertwiner and
`smoothFunctorForgetIso` recovers the original locally constant sheaf functor
when the smoothness proof is forgotten.

The provenance is internal: this combines the imported actual locally constant
sheaf, its labeled restrictions and coefficient maps, the existing local-fixedness
definition and stable-neighborhood property, and the original open-subgroup
smoothness predicate for coefficients. It adds no original-literature assertion.
It is an ordinary-open construction; analytic or etale comparisons, acyclicity,
derived equivalences, arithmetic towers and Harris specialization remain separate.
