# Algebraic coefficient integrals

This internal construction supplies finite-dimensional coefficient integration
for the corrected essential-vector argument. It is elementary algebra and scalar
Bochner integration. It imports only Mathlib and does not assert a
representation-theoretic or analytic statement about the Rankin–Selberg integral.
The intended application is the finite-dimensional Laurent coefficient spaces
appearing in Jacquet's corrected construction; the definitions here work for any
complex vector space.

Let `X` be an arbitrary measurable space, `μ` any measure on it, and `A` a complex
vector space, with no topology assumed on `A`. `IsScalarIntegrable μ f` means
that `x ↦ L (f x)` is Bochner integrable for every algebraic complex linear
functional `L : A →ₗ[ℂ] ℂ`.

For a finite basis `b` of `A`, `basisCoefficientIntegral μ b f` is

`∑ i, (∫ x, b.repr (f x) i ∂μ) • b i`.

This expression is defined for every function using Mathlib's total scalar
integral. Its interpretation as an integral, and basis independence, use the
stated scalar-integrability hypothesis. In
`basisCoefficientIntegral_linear_eval`, expansion in the basis gives a finite
sum for `L (f x)`. The coordinate functionals give integrability of each
summand; linearity of the scalar integral for finite sums and scalar
multiplication gives

`L (basisCoefficientIntegral μ b f) = ∫ x, L (f x) ∂μ`.

Applying this identity to all coordinate functionals of a second finite basis
proves `basisCoefficientIntegral_eq`.

When `Module.Finite ℂ A` holds, `finiteDimensionalCoefficientIntegral` uses
`Module.finBasis ℂ A`. Its evaluation identity is the preceding theorem.
`IsScalarIntegrable.linear_map` composes scalar functionals with an algebraic
linear map. `finiteDimensionalCoefficientIntegral_map` uses that preservation
and the coordinate functionals of the target to prove naturality for linear
maps between finite-dimensional complex vector spaces.

For a function with finite-dimensional span of its range,
`coefficientSpanFunction f` regards it as valued in that span.
`finiteSpanCoefficientIntegral μ f` integrates in the span and then includes
the result in `A`. Its evaluation theorem requires scalar integrability of
this span-valued function; this hypothesis is explicit and is not inferred
from any compactness assertion in this unit. Composing an ambient functional
with the span's inclusion proves the stated evaluation identity.
Finally, `finiteSpanCoefficientIntegral_mem` says that any complex submodule
containing every value also contains the integral. The span is contained in
that submodule, so this conclusion needs no integrability hypothesis.

The actual determinant-level quotient integrand, finite-dimensionality of its
value span, scalar integrability, its spherical specialization, and the
subsequent formal transform and essential-vector conclusions remain separate
obligations.
