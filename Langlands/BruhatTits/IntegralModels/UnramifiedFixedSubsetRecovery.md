# Recovered models of coefficient-fixed apartment subsets

Author: Worker 200.

This internal supporting unit constructs actual compatible lower and upper
component models for a nonempty apartment subset whose points are individually
fixed by the coefficient action. The subset is bounded under every real affine
function. The entry definition is
`recoveredFixedSubsetModelsOfVertexInputs`.

Four unproved inputs remain explicit hypotheses:

- `MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement`;
- `MaximalBoundedIntegralModelStatement`;
- `IntegralModel.SmoothIntersectionStatement`;
- `IntegralModel.UnramifiedSmoothModelDescentStatement`.

The other assumptions are the actual upper apartment and its centralizer with
integer-valued V6 compatibility, a maximal upper split torus, and connected
reductivity of the original group over the nonarchimedean local field. No lower
apartment, building, or root valuation is assumed.

`KPApartmentData.galoisStable_of_fixed` first obtains stability of the full
valuation class from one fixed point: its transform is equal to the point,
so it is equipollent to that point. The published criterion
`galoisStable_iff_equipollent` then applies.

`rationalConjugate_mem_characterKernel_inf_pointwiseFixer_iff` works over an
arbitrary field extension with an invariant valuation and a supplied stable
apartment. The actual quotient coefficient action fixes each image of a
coefficient-fixed apartment point. Its semilinearity transports full point
stabilizers. Together with the actual character-valuation-kernel comparison,
this gives preservation and reflection of the full norm-one pointwise fixer.
This lemma allows any subset, including the empty one, once apartment stability
is supplied.

`exists_recovery_of_fixedSubset` requires a supplied upper component model whose
full integral image is exactly the norm-one pointwise fixer of the apartment
image of a nonempty fixed subset. It derives apartment stability from one member
and uses the invariant maximal-unramified valuation to obtain coefficient
stability of that full image. The conditional published component-descent
theorem then recovers both full and neutral models, with their actual inclusion
square, over the identity of the original generic group. It does not assume
separate coefficient stability of neutral integral points.

`RecoveredApartmentFixerModels` records actual lower and upper relative-component
models, their compatible unramified recovery, and the exact upper full-image
equality. It does not assert a formula for the neutral integral image.

`exists_recoveredFixedSubsetModels_of_vertexInputs` and the chosen entry
definition construct this package by applying the existing full-model
construction to `MaximalUnramified.buildingDataOfApartment` and the identity
translate of the supplied subset. The finite-vertex approximation and
finite-index-enlargement inputs are discharged by the published theorems
`MaximalUnramified.finiteVertexFixerApproximation` and
`IntegralModel.finiteIndexEnlargement`. The three other full-model inputs remain
explicit. Geometric connectedness of the original group follows from its
connected reductivity and the published finite-type group theorem; smooth
descent remains the fourth explicit input.

The finite-subset constructor proves affine boundedness because each affine
image is finite. The singleton and two-point constructors specialize it. In
particular the two endpoints may coincide. No full-fixer constancy on a facet
closure is used.

This is derived internal content, composed from the published quotient action,
character-kernel comparison, full-model construction, smooth-descent interface,
component recovery and the separately submitted apartment-data adapter. It is
not a new transcription of a literature statement. It supplies neither the
four retained input theorems nor parabolic special-fibre images, exact reduction
preimages or the unconditional fixed-point depth-zero opposite-factor theorem.
