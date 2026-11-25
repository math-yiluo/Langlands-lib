# Recovered fixed-subset models from published construction proofs

This module discharges all four global construction premises
of `UnramifiedFixedSubsetRecovery` using published theorems. It supplies actual
recovered models for nonempty bounded subsets of the given upper apartment
whose points are individually fixed by the original coefficient action.

The field `F` is any nonarchimedean local field in universe `u`. The original
affine group `G` is connected reductive. The supplied inclusion of `T`, after
base change to `inertiaFixedField F`, is a maximal split torus and an underlying
scheme monomorphism. The supplied upper apartment `D` satisfies integer-valued
omega compatibility with the supplied centralizer `C`. These geometric
assumptions remain explicit; no lower apartment or building is assumed.

`exists_recoveredFixedSubsetModels` applies the published
`exists_recoveredFixedSubsetModels_of_vertexInputs` with the following proofs:

- `MaximalUnramified.vertexOneStabilizerMaximalBounded` from
  `UnramifiedVertexMaximalBoundedProof`;
- `Langlands.GroupScheme.maximalBoundedIntegralModel` from
  `MaximalBoundedConstruction`;
- `IntegralModel.smoothIntersection` from `SmoothIntersectionConstruction`;
- `IntegralModel.unramifiedSmoothModelDescent` from
  `UnramifiedSmoothDescentProof`.

The boundedness assumption requires the image of the subset under every real
affine function to be bounded above. The fixedness assumption is equality of
each actual valuation family with its transform under every coefficient
automorphism over `F`, rather than only setwise invariance of the subset.

The entry definition `recoveredFixedSubsetModels` chooses a witness of this
existence theorem. Its result is the existing
`RecoveredApartmentFixerModels D Ω` structure: actual lower and upper relative
component models, compatible recovery of their full and neutral models over the
generic identity, and the exact upper full integral-point subgroup

`characterValuationKernel (MaximalUnramified.valuation F) G_K ⊓
D.pointwiseFixer (D.apartmentMap '' Ω)`,

where `G_K` is the original group base changed to `inertiaFixedField F`.

`recoveredFixedFiniteSubsetModels` proves boundedness by finiteness of every
affine image. `recoveredFixedPointModels` and `recoveredFixedPairModels`
specialize it to a singleton and two individually fixed endpoints. The two
endpoints may coincide.

This is a composition of existing Library proofs and interfaces, with no new
literature claim. The construction has no extra vertex, maximal-bounded-model,
intersection or descent premise, and imposes no residue-characteristic
restriction. It does not identify neutral integral points with a zero fixer,
construct prescribed integral tori, prove quotient-root survival, or establish
the special-apartment chamber statement.
