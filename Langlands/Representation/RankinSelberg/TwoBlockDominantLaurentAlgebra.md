# Laurent reflection in the dominant-rank assembly

This module develops elementary coefficient algebra for the dominant-rank
assembly. It is an internal derivation from the published
`BilateralLaurentSeries` module and Mathlib's Laurent polynomial algebra.
It supplies no analytic Fourier identity, coefficient uniqueness theorem,
gamma comparison or L-polynomial divisibility.

For a nonzero complex unit `q`, `bilateralReflection q` sends a coefficient
function `a` to the function `n ↦ q^n * a(-n)`. It is a complex linear
equivalence whose inverse is itself. No support or convergence assumption is
made on the bilateral series.
`eq_bilateralReflection_iff` identifies this equality with the equivalent
coefficient law `b(-k) = q^(-k) * a(k)`, by replacing the index by its negative.

`laurentReflectionMonomial` sends the multiplicative exponent `m` to the
Laurent monomial `q^(-m) * X^(-m)`. The additive monoid algebra universal
property extends this map to the complex algebra homomorphism
`laurentReflection q`. Thus this homomorphism implements the substitution
`X ↦ q⁻¹ X⁻¹`. The constant and monomial evaluation laws specify its
normalization.
The homomorphism is involutive: Laurent induction reduces this to
`q^(-m) * q^m = 1` on monomials.

`bilateralReflection_laurent_smul` proves that reflection transports the
Laurent action through this substitution. Laurent polynomial induction
reduces the proof to addition and a single monomial. The monomial case
uses `q^(-m) * q^(n+m) = q^n` and the equality of the shifted indices.
Only finite Laurent multiplication is involved.

`coeffwiseIntegrable_bilateralReflection` preserves coefficientwise
integrability for any measurable domain and any supplied measure, because
each reflected coefficient is a scalar multiple of an integrable coefficient.
`coeffwiseIntegral_bilateralReflection` commutes reflection with the total
coefficientwise Bochner integral, using the constant multiplication law for
each coefficient. These general algebraic identities introduce no analytic
assertion about a JPSS section or a particular measure.

`laurent_cleared_comp` combines two equations
`A • b = B • a` and `C • c = D • b` into
`(A*C) • c = (D*B) • a`. The proof multiplies each equation and commutes
the scalar actions. `laurent_cleared_reflection_comp` first reflects the
first equation and then applies this composition. Every denominator factor
remains in the conclusion. In particular, the proof never cancels a
Laurent polynomial acting on a bilateral series; the published module
contains an explicit torsion example showing why cancellation would fail.

These helpers prepare the coefficient algebra for a later use of actual
Section 4 analytic identities. No analytic identity is a premise of either
final dominant-rank target, and neither final target is proved here.
