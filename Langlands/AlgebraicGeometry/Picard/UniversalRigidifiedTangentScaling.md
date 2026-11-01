# Actual epsilon pullback for the universal tangent comparison

This internal construction applies over an arbitrary field `k`, for a scheme
`X` with a section and any actual universal rigidified family on `P`. It extends
the actual additive tangent/deformation comparison by proving its underlying
line-bundle class formula for every field scalar, including zero.

`dualNumberTestScale c` is the actual endomorphism of the dual-number test scheme
over `Spec k` obtained by taking spectrum of the algebra endomorphism
`a + ε b ↦ a + ε (c b)`. Its slice condition follows from the algebra homomorphism
commuting with the field algebra map. `rationalStalkDerivationPoint_smul` is the
slice-valued version of the published scalar formula for actual stalk derivations:
the point of `c • D` is the point of `D` precomposed with this endomorphism.

`relativeSpaceSymmetry_scale` proves by the two fibre-product projections that
this relative endomorphism corresponds under fibre-product symmetry to the
actual thickening map `DualNumberThickening.scale f c`.
`underlyingDualNumberClassEquiv_scale` combines that equality with naturality of
forgetting rigidification and composition of actual line-bundle pullback. Thus
pullback along the test endomorphism becomes pullback of the ordinary class
along the actual scaling endomorphism of the thickening.

`tangentDeformationEquiv_smul_val` now follows from linearity of the actual
sheaf-tangent to stalk-derivation equivalence, the stalk scalar formula,
naturality of universal classification, and the forgetting formula just proved.
It states equality in the actual line-bundle isomorphism class group; the
existing deformation equivalence already ensures membership in the deformation
subgroup on its left side. No auxiliary module structure is imposed on that
subgroup. A subsequent composition can use this formula together with the
scalar formula for its derived H1 comparison.

All maps and compatibility results are proved from imported constructions.
No additional literature-specific assertion or hypothesis is introduced.
