# Transport on actual coefficient models

This internal derived helper connects evaluation on a coefficient image with
its original Whittaker functions and transports the actual normalized matrix
functional-equation data. It uses the published coefficient construction and
coefficient-space transport results, together with the preceding Models helper.
It contains no analytic existence result or matrix-to-Whittaker integral
comparison.

`coefficientMap_coefficientModelEvaluation` proves that the coefficient map
associated to evaluation at identity on the coefficient image is just the
inclusion into the ambient equivariant function space. The calculation is
`W(1*g)=W(g)` for the actual right-translation action.
`coefficientModel_coefficientModelEvaluation` consequently identifies the
resulting double coefficient model with the original coefficient model, as
subrepresentations of that same function space. The proof checks both range
inclusions.
`coefficientModelEvaluation_ne_zero` pulls back a hypothetical zero evaluation
functional along the surjective model map; its pullback identity contradicts
nonzeroness of the original functional.

`nonzeroFunctionalModelEquiv` is the representation equivalence between the
actual coefficient images of two nonzero functionals of a full Whittaker-type
representation. Full Whittaker type gives equality of these coefficient
subrepresentations, and the induced linear equivalence is the identity on
underlying functions. This assumes no equivalence of the original representation
with its coefficient image.

`GodementJacquet.normalizedMatrixFunctionalEquationData_equiv` proves that a
representation equivalence preserves the complete normalized matrix data.
The published equality of actual bi-smooth coefficient submodules preserves
both analytic assertions, the actual inverse-transpose coefficients, and the
equation for every Fourier test and every continuation. The matrix Fourier
relation, scalar measure, polynomials, unit and integer exponent are identical.
`normalizedMatrixData_nonzero_functional_iff` applies this to the actual
canonical p-adic models of two nonzero standard Whittaker functionals.
The field and original carrier universes remain independent.
