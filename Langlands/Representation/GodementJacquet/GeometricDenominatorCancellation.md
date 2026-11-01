# Cancellation of reciprocal geometric Laurent denominators

This internal algebraic helper works in the existing complex Laurent ring and
its genuine embedding into the rational function field. It uses no analytic or
representation theoretic assumptions.

`laurentReciprocal δ` substitutes `δ/T` within the Laurent ring for a nonzero
complex scale `δ`. The proof shows that this operation commutes with the
published rational substitution `RationalReflection.subst`.

Suppose multiplication of a rational function `R` by each of
`D = 1 - α*T(k)` and `E = 1 - β*T(-k)` produces a Laurent polynomial. When
`α*β ≠ 1`, the identity
`E + β*T(-k)*D = 1 - α*β` proves that `R` itself is Laurent. The implemented
proof explicitly constructs its Laurent numerator from the two supplied
numerators and the inverse of the nonzero constant.

The final theorem applies this identity to a second rational function related
by a supplied Laurent-unit functional equation. Reciprocal substitution sends
its denominator `1 - β*T(k)` to
`1 - β*δ^k*T(-k)`. The supplied Laurent unit can be inverted within the
coefficient ring, so the two denominator clearings cancel when
`α*β*δ^k ≠ 1`.

These assertions are derived by ring arithmetic from the imported Laurent
embedding, Laurent monomial units and rational reciprocal substitution. This
pair does not prove a functional equation, the nonvanishing condition for any
particular matrix denominator, or the analytic existence of rational values.
