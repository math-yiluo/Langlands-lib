# The pointwise tensor map for normalized refined induction

This internal adapter constructs the actual intertwining map
`Langlands.Parabolic.RefinedInductionTensor.pointwiseMap` from the external
tensor of the normalized block inductions to the normalized refined
induction in the published comparison statement. It does not prove
bijectivity or the comparison theorem.

Fix the actual p-adic field, compatible topology, outer block shape,
refinement, and smooth complex inner-Levi factor family from
`RefinedInductionTensorStatement`. The field and coefficient universes
remain independent, and every finite family, including the empty family,
is included. The construction uses the original coefficient and induced
function carriers, with no dimension, admissibility, irreducibility, or
finite-length assumptions.

The actual refined parabolic is definitionally the product subgroup
`Subgroup.pi Set.univ` of the inner parabolics. Its coordinate maps
`refinedParabolicEval` agree with the generic `productSubgroupCoordinate`;
their subtype membership proofs do not affect the elements.
`productInducing_eq` first identifies the generic product inducing
action with `coordinateInducingRepresentation` on pure tensors, and then
uses the published `coordinateInducingRepresentation_eq` to identify it
with the actual normalized refined inducing action. This retains the
positive half-modulus convention.

`inducingNormalizationEquiv` is the identity linear equivalence on the
original indexed tensor coefficient space. Equality of the two inducing
actions proves its equivariance.
`inducedNormalizationEquiv` applies the published
`Induction.smoothInducedEquiv` to this identity coefficient equivalence.
Thus it changes the covariance certificate while keeping the values of
the induced function.

`pointwiseMap` composes the published `Induction.finiteProductTensorMap`
with that induced normalization equivalence. Its source and target are
exactly `externalRepresentation` and `refinedRepresentation` in the
published target. The resulting `pointwiseMap_tprod_eval` states that a
pure tensor of block functions evaluates at a tuple to the tensor of
the corresponding block evaluations. The implemented proof reduces evaluation
through the identity coefficient equivalence definitionally, then applies
`finiteProductTensorMap_tprod_eval`.

The provenance is internal: the construction combines the published
actual product map, normalization equality, and functorial transport of
smooth induction. It makes no new attribution to the original literature
and asserts no tensor identity for unrestricted function spaces.
Compact-quotient bijectivity and the final comparison remain separate
proof obligations.
