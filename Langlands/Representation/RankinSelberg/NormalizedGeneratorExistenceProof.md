# Normalization of a fractional Laurent span containing one

This internal algebraic proof targets the published
`Langlands.RankinSelberg.NormalizedGeneratorExistenceStatement`.
It imports that statement and the existing `RationalZeta` algebra unchanged.

The proof first writes a nonzero Laurent polynomial as an ordinary polynomial
times a negative power of the variable. It factors out the ordinary polynomial's
root multiplicity at zero, leaving a polynomial whose constant coefficient is
nonzero. Multiplication by the inverse of that coefficient normalizes the
constant coefficient to one. The factors removed are a power of the Laurent
variable and a nonzero complex scalar; their product is a Laurent unit.

For an arbitrary set of rational functions with a common Laurent denominator,
`exists_rationalGenerator` supplies a rational generator of its Laurent span.
Membership of one in that span gives a Laurent scalar whose product with this
generator is one, so the scalar is nonzero. Applying the normalization just
described writes it as a Laurent unit times a polynomial with constant
coefficient one. Multiplying the rational generator by that Laurent unit gives
the reciprocal of the polynomial. Multiplication by a unit preserves the
generated submodule, proving the exact normalized-generator conclusion.

This is the algebraic implication isolated by the existing statement from the
normalization argument in JPSS, *Rankin–Selberg Convolutions* (1983), proof of
Theorem 2.7. The mathematical provenance and original page references are
documented in `NormalizedGeneratorExistenceStatement.md`. The present proof
uses only the published algebra and Mathlib's Laurent-polynomial, polynomial
root-multiplicity and singleton-span lemmas. It proves neither the analytic
common denominator nor the unit membership for any particular family of
integrals. No finiteness hypothesis on the original set is added.

Author: Worker 64.
