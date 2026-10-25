# Coordinate normalization for refined tensor induction

This is an internal adapter for the published
`Langlands.Parabolic.RefinedInductionTensorTheorem`. It defines the action that
will occur in the pointwise tensor-induction construction and identifies it with
the inducing action in that target. It does not construct the induction map or
prove its bijectivity.

Fix an actual p-adic field `F`, compatible topological data `T`, an outer block
shape `B`, a refinement `S`, and a family `A` of smooth complex representations of
the inner Levi groups. The field and coefficient universes `uF` and `uV` remain
independent. All finite block families, including the empty family, are covered;
no finite-dimensionality, admissibility, or irreducibility is assumed.

`blockInducingRepresentation` is the inner Levi representation inflated to its
block parabolic and twisted by the existing positive half-modulus.
`coordinateInducingRepresentation` is the indexed tensor of those actions,
pulled back to the actual refined parabolic by `refinedParabolicEval`.
`normalizedRefinedInducingRepresentation` abbreviates the target's inducing
action: inflate the external tensor transported to the actual refined Levi,
then twist by the refined positive half-modulus. These use the existing carriers
and coordinates without any replacement representation data.

Three coordinate identities in `Langlands.PadicField.TopologicalData` support
the comparison. `refinedLeviBlock_projection` identifies the inner Levi coordinate
of the actual refined projection with the corresponding block Levi projection.
Its proof cancels the inverse of `refinedLeviEquiv`.
`refinedLeviHalfModulus_eq_prod` proves equality in the complex units between
the refined positive half-modulus and the product of the block positive
half-moduli. The explicit refined modulus is already defined as a product;
positive square root and inclusion into the complex numbers are monoid
homomorphisms, so their maps on units preserve that product.
`refinedParabolicHalfModulus_eq_prod` pulls this identity back through the
projection and uses the coordinate identity.

Finally, `coordinateInducingRepresentation_eq` proves equality of the two
representations. Extensionality reduces the claim to a pure tensor. The tensor
action applies each block action, and multilinearity extracts the product of
the scalar normalizers. The parabolic half-modulus identity identifies that
product with the refined normalizer; the inverse coordinate equivalences
identify the remaining actions. This is equality of the inducing actions,
without any assertion about smooth-induction surjectivity or compact quotients.

The provenance is internal and derived directly from the published definitions
in `Geometric.RefinementDefinitions`, `Geometric.RefinementFunctors`,
`Parabolic.RefinedInductionTensorStatement`, `Tensor.Finite`, and
`Twist.Definitions`, together with Mathlib's tensor and monoid-homomorphism
identities. No separate formula from the original literature is claimed here.
