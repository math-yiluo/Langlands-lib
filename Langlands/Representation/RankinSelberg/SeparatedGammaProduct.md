# Separated roots in an equality of gamma expressions

`eq_of_separated_rationalGammaExpression` is an internal algebraic lemma for comparing two actual Rankin–Selberg gamma expressions. Let `P, D` be the first pair of polynomials, `B, BD` the second pair, and `δ` a complex unit. Assume `P, D, BD` have constant term one and `B = Q * P` for a normalized `Q`. If no nonzero root `x` of `B` is a root of `BD` after reflection `x ↦ δ / x`, equality of the gamma expressions implies `P = B` and equality of the two epsilon data pairs.

The Lean proof clears the reflected denominators, which are nonzero as rational functions by normalization and the reflection automorphism. It cancels `P` before evaluating. A nonconstant `Q` would have a complex root, necessarily nonzero. All factors of the cleared identity are regular there; the identity then gives `BD(δ / x) = 0` since the epsilon monomial is nonzero. This contradicts separation. Thus `Q` is constant and normalization gives `Q = 1`. The proof then uses `rationalGammaExpression_cancel`, which compares epsilon data using normalized dual polynomials without assuming that the dual polynomials coincide in advance.

This is a derived algebraic step, not a separate statement attributed to JPSS. It combines the Library's rational evaluation, reflection, and cancellation lemmas for use with JPSS (1983), Theorem (3.1)(i)–(ii).
