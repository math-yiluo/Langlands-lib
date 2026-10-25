# Laurent-span criteria for polynomial divisibility

This module proves the published
`Langlands.RankinSelberg.LaurentPolynomialDivisibilityStatement` without
additional hypotheses. Its theorem `laurentPolynomialDivisibility` combines
the three component proofs in the published order. All names below are in
`Langlands.RankinSelberg`.

Write `ι` for `algebraMap ℂ[X] RationalFunctions`. The coefficient ring is the
actual `LaurentCoefficients`, its action on `RationalFunctions` is through
`laurentToRatFunc`, and its polynomial embedding agrees with `ι`.

`reciprocalLaurentSpanClearing` proves, for nonzero polynomials `P` and `A`,
that `ι(P)⁻¹` belongs to the Laurent span of `ι(A)⁻¹` if and only if there
exist a polynomial `Q` and a natural number `e` with `X^e * A = Q * P`.
For the forward direction, singleton-span membership gives a Laurent scalar
`a`. Cancelling the nonzero reciprocals gives `laurentToRatFunc a * ι(P) =
ι(A)`. Mathlib's `LaurentPolynomial.exists_T_pow` provides a nonnegative
exponent `e` and a polynomial `Q` with `Q.toLaurent = a * T e`. Mapping
this equation to rational functions and using injectivity of the polynomial
embedding yields the required polynomial identity. Conversely, that identity
provides the explicit Laurent multiplier `Q.toLaurent * T (-e)`.
The image of this multiplier is `ι(Q) * (X^e)⁻¹`. The embedded polynomial
identity and cancellation of the nonzero images of `X^e`, `A`, and `P`
prove the singleton-span membership.

`normalizedReciprocalLaurentSpanDivisibility` proves that, under
`P.coeff 0 = 1` and `A ≠ 0`, the same membership is equivalent to `P ∣ A`.
Normalization implies that `P` is nonzero. For the forward implication the
clearing result gives `P ∣ A * X^e`. The polynomial identity
`X * P.divX + C (P.coeff 0) = P` supplies the Bezout coefficients
`1` and `-P.divX` for `P` and `X`. Thus `P` is coprime to `X^e`, and
Mathlib's `IsCoprime.dvd_of_dvd_mul_right` removes the power of `X`.
For the reverse implication a polynomial divisibility witness supplies the
clearing equation with exponent zero.

`normalizedGeneratorSpanDivisibility` proves that for arbitrary sets `S, T`
of rational functions, normalized-generator hypotheses for `P, A` imply
`zetaSpan S ≤ zetaSpan T ↔ P ∣ A`. The generator hypotheses identify both
spans with their reciprocal singleton spans. The theorem
`Submodule.span_singleton_le_iff_mem` reduces inclusion to membership of
`ι(P)⁻¹` in the span of `ι(A)⁻¹`; the preceding normalized criterion applies,
using the nonzero polynomial consequence of the second generator hypothesis.

## Internal provenance and scope

Worker 468 authored this proof. The denominator-clearing calculation and the
explicit coprimality calculation materially adapt Worker 31's private
`polynomial_dvd_of_laurent_multiple` and
`polynomial_dvd_of_reciprocal_mem` proofs in the published
[RationalZeta](RationalZeta.md). The new proof neither refers to those private
Lean declarations nor modifies that module. The converse clearing implication
uses an explicit negative Laurent power; the remaining implications assemble
the algebra described above. Worker 356 authored the published statement pair
with the interface specified by Worker 46.

This is an internal algebraic consequence of the published
[LaurentDivisibilityStatement](LaurentDivisibilityStatement.md) and its
`RationalZeta` constructions. It introduces no separate literature claim,
analytic existence assertion, or multiplicativity result. The coefficient
field, the actual Laurent action, both implications in each criterion, the
nonnegative exponent and polynomial witness, arbitrary rational-function sets,
and the direction `P ∣ A` all agree with the published target. No target or
imported Lean/Markdown pair is changed.
