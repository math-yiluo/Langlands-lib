# Linearity and right translation of the actual adjacent Jacquet integral

This internal module derives linearity and right evaluation from the literal
scalar kernel of `AdjacentRankJacquetEvaluation`. All sections belong to the
same canonical normalized opposite-parabolic induction on the original tensor
carrier. The field and module universes remain independent; no topology or norm
is placed on the original module.

`inducedRepresentation` abbreviates the exact host representation without
changing its carrier or action.

`sectionCoefficientLinear` bundles evaluation through the original-carrier
coordinates and the specified Whittaker functional as a complex linear map.
`sectionCoefficient_right` proves that right translation of a section by `k`
evaluates at `g*k`. Both follow from the actual induced action and the linear
coordinate and functional maps.

`integrandLinear` bundles the literal kernel
`sectionCoefficient f (upperColumn x * g) * psi(-x_last)` as a linear map to
scalar functions of `x`. `integrand_right` identifies the kernel of a translated
section with that at `g*k` by associativity.

`integral` is the scalar Bochner integral against the supplied product row Haar.
`integral_right` integrates the exact right-translation identity, without a
convergence premise. `integralLinear` bundles integration as a linear map under
the explicitly local hypothesis that the literal kernel is integrable for
every actual section and every ambient element. Its proof uses `integral_add`
with that hypothesis and `integral_smul`. The later image proof must discharge
this hypothesis using pure-section convergence and section spanning; this
module claims no unconditional all-section convergence.

`integralLinear_coefficient` proves that the functional given by the integral
at the identity evaluates on `rho(g) f` to the literal integral at `g`.
Whittaker covariance and nonvanishing are separate obligations.
