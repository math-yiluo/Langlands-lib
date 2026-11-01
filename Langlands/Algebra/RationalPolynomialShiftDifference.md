# Positive-step differences of rational polynomials

This internal arithmetic construction supports induction on dimension for the
ample Euler polynomial. It is derived from Mathlib's polynomial translation,
Hasse derivative, degree and ordered rational arithmetic APIs; it asserts no
additional geometric input.

`shiftDifference P e` is the polynomial `P(X + e) - P(X)`. Its evaluation lemma
holds for every rational argument and step. Equality with this polynomial follows
from the corresponding equality on any natural-number tail, by the published
rational-polynomial uniqueness theorem.

If `P.natDegree ≤ d + 1`, `shiftDifference_coeff` proves that its coefficient at
`d` is `(d + 1) * e * P.coeff (d + 1)`. The implemented proof translates this
coefficient into evaluation of the `d`th Hasse derivative. The derivative has
degree at most one; its two coefficients give the formula after subtracting the
original coefficient.

For a positive rational step, if the difference has natural degree `d` and positive
leading coefficient, then `P` has natural degree `d + 1` and positive leading
coefficient, and the difference's leading coefficient is
`(d + 1) * e * P.leadingCoeff`. The proof makes the coefficient at `d + 1`
positive, uses its nonvanishing to force equality in the original degree bound,
and then identifies both leading coefficients.

The final theorem expresses this result for positive natural `d` and `e`, a
polynomial `Q` of degree `d - 1`, and an eventual evaluation identity
`Q(n) = P(n + e) - P(n)`. It concludes exact degree `d`, positive leading
coefficient, and `Q.leadingCoeff = d * e * P.leadingCoeff`. Equality at every
natural number is a special case of the eventual hypothesis.
