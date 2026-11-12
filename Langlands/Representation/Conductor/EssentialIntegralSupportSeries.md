# Polynomial coefficients forced by the essential identity

Worker 1466.

This internal helper unit derives polynomial Satake coefficients for the actual
corank-one Laurent series of a smooth Whittaker-model vector. Its inputs are an
`IsJacquetNormalization`, a complex polynomial `P` with `P.coeff 0 = 1`, and
`SatisfiesEssentialIdentity` for that polynomial and vector. It applies to every
nonarchimedean local field, with independent field and representation-space
universes. It imposes no restriction-invariance or last-row-support hypothesis.

The construction `symmetricPolynomialTorusSubalgebra σ K` is the range of the
published algebra homomorphism `symmetricPolynomialToTorus σ K`. Thus its elements
are symmetric Laurent polynomials that arise from actual symmetric multivariate
polynomials. This is an internal range construction, not a new assertion
attributed to the literature.

The analytic helpers first prove that finite polynomial multiplication commutes
with a convergent bilateral Laurent sum. For each exponent of the polynomial,
translation of the integer index and multiplication by a scalar preserve
`HasSum`; summing those finitely many identities gives the convolution formula.
`hasSum_mapped_laurent_mul_polynomial` combines it with the published coefficient
formula for `finitePolynomialLaurentSeries`.

`essentialFactor_eval_mul_denominator` evaluates the rational-function identity
that the essential factor times its coordinate denominator is one. The
normalization `P.coeff 0 = 1` makes the coordinate denominator nonzero. The
conclusion is asserted only where the reduced denominator of the essential
factor is nonzero, so the evaluation-of-product theorem applies.

`corankOneModelDenominatorProduct_eq_one_of_essentialIdentity` identifies the
actual formal denominator product with one. Fix a unit Satake tuple and
specialize its coefficients to complex numbers. The published smooth-model
support theorem gives a lower bound for this Laurent series. For sufficiently
large real `s`, the defining integral converges, the essential identity holds,
and its essential factor is regular. The published degree-integral expansion,
followed by finite convolution, shows that the evaluated product sums to one.
After subtracting the constant Laurent series one, scalar Laurent uniqueness
on a sufficiently small positive real interval makes each specialized
coefficient zero. Separation by all unit tuples then gives the equality in the
symmetric Laurent coefficient algebra.

`degreeCorankOneModelCoefficient_mem_polynomial_of_essentialIdentity` extracts
polynomial membership from that equality. The coordinate denominator has
constant coefficient one, and all its coefficients lie in
`symmetricPolynomialTorusSubalgebra`. At degree `d`, isolate its constant term
in the finite convolution. This expresses the model coefficient as the
coefficient of one minus a finite sum involving only strictly smaller degrees.
Induction from the published common lower bound proves membership at every
integer degree. The implemented closure step expresses subtraction using
addition and multiplication by the complex scalar `-1`.

Finally,
`degreeCorankOneModelCoefficient_eq_polynomial_of_essentialIdentity` unpacks
range membership and forgets the symmetry proof. For every degree `d` it
produces an ordinary multivariate polynomial whose image in the torus
coordinate algebra equals the underlying model coefficient. This is the
interface used by the independent finite-Schur-expansion support reduction.

All results here are derived from the published actual model-series,
denominator, integral-expansion and separation interfaces and ordinary
Mathlib algebra and convergence results. They do not use existence of an
essential vector, the 1981 existence argument, compact-subgroup invariance of
that vector, or the conductor theorem. This unit supplies a coefficient
property; it does not itself assert the final integral last-row support theorem.
