# Ordinary matrix analytic data on actual Whittaker models

Author: Worker 468.

This internal construction assembles the ordinary
`GodementJacquet.Padic.MatrixAnalyticAssertions` on the actual carrier
`(glCoefficientModel psi n sigma ell).toSubmodule`. The original
representation `sigma` has full Whittaker type and may be reducible. The
field and original carrier have independent universes, and every natural
`n`, including zero, is allowed. The additive character is the supplied
nontrivial unitary character, and the measures and absolute value are the
canonical ones in the published matrix definitions. The spectral exponent
is exactly `s + jpssShift n`.

`modelMatrixRationalValue` chooses an actual rational value for any
full-matrix Schwartz--Bruhat test and any actual bi-smooth coefficient of
the specified model at a nonzero functional. Its specification retains
both `HasShiftedRationalValue`, including convergence and the rational
continuation's denominator condition, and membership in the original
Whittaker ideal `jpssI3 F psi sigma ell`.

## Implemented proof

`exists_modelMatrixRationalValue` first applies the published
`exists_mem_jpssI3_of_coefficient` to an individual coefficient
`g ↦ Lambda(rho(g)w)`. The model is admissible by
`glModel_isAdmissible`, since the original representation is admissible.
The published closed theorem `GodementJacquet.modelWhittakerRationality`
discharges the local `ModelRationality` premise at the same original
representation and nonzero functional. The compact-averaging argument in
`WhittakerModelInclusion` therefore supplies an actual shifted rational
value in `jpssI3` for each individual coefficient.
`exists_hasShiftedRationalValue_mem_of_generators` extends this assertion
to the entire complex coefficient span. Classical choice and its
specification give `modelMatrixRationalValue` and
`modelMatrixRationalValue_spec`.

`modelMatrixAnalyticAssertions` supplies the three conjunction components
of the existing analytic predicate. Common convergence comes from
`WhittakerTorus.Padic.glModel_matrixConvergesOnRight`. The chosen rational
values supply continuation for every test and coefficient. Finally
`modelMatrixLPolynomial_normalized` supplies the normalized generator.
`exists_modelMatrixAnalyticAssertions` chooses the previously constructed
`modelMatrixLPolynomial` before the functional and retains its complete
`IsPadicSymmetricLPolynomial` certificate against the trivial rank-one
character with the supplied self-dual additive Haar measure.

## Provenance and scope

This is derived internal support obtained by composing the named
published and companion constructions; it claims no separate literal
literature theorem. The closed model rationality proof discharges its
Whittaker asymptotic and pointwise Mellin interfaces using
`whittakerTypeAsymptotic` and `finiteFunctionMellin`. The normalized
generator construction uses the published ideal comparisons and full
symmetric pair L-existence proof. Common convergence uses the fixed
slice exponents and finite torus family from
`UniformWhittakerMatrixConvergence`, whose explicit premise
`UniformFiniteFunctionMellinConvergenceStatement` remains required here
as `hU`. Per-pair continuations alone are not used to infer that common
bound.

The constructed rational values require no uniform Mellin premise.
The assembled analytic assertions retain it explicitly. This module
supplies neither inverse-transpose analytic data nor a functional
equation, and proves neither closed two-block rank-one base proposition.
No two-block or finite-block multiplicativity theorem is used.
