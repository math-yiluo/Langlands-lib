# Uniqueness and dilation of rational polynomials

This internal proof establishes
`Langlands.Algebra.RationalPolynomialDilationStatement`.

`RationalPolynomial.eq_of_eventually_nat_eval_eq` obtains a threshold from
the eventual equality. The rational images of the natural numbers at or
above that threshold form an infinite set, because natural-number
inclusion into `ℚ` is injective. The equality set of polynomial
evaluations contains that infinite set. Mathlib's
`Polynomial.eq_of_infinite_eval_eq`, which follows from the finite root
bound, identifies the two polynomials.

`RationalPolynomial.eq_comp_of_eventually_nat_eval_dilation` rewrites
evaluation of `P.comp (C q * X)` as evaluation of `P` at `q*n`. It then
applies the preceding uniqueness result.

`RationalPolynomial.dilation_natDegree_leadingCoeff` uses positivity of
`q` to show its rational image is nonzero. Mathlib's natural-degree
composition formula gives unchanged degree, since `C q * X` has natural
degree one. The explicit coefficient formula
`Polynomial.comp_C_mul_X_coeff` multiplies coefficient number `i` by
`q ^ i`. Taking `i = P.natDegree` gives the leading-coefficient formula.
These steps also apply when `P` is zero.

`RationalPolynomial.scalar_eq_pow_of_eventually_nat_eval_dilation`
identifies `Q` with the dilation composition. Its leading-coefficient
formula and the assumed scalar comparison give
`P.leadingCoeff * r = P.leadingCoeff * q^g`. Nonzeroness of `P` makes
its leading coefficient nonzero, so cancellation in `ℚ` identifies the
two rational scalars. Injectivity of the natural-number inclusion gives
`r = q ^ g` in `ℕ`.

The final theorem groups these four results without extra outer
hypotheses. The argument includes `q = 1` and degree `g = 0`. It proves
only the stated polynomial arithmetic; it does not supply any scheme
Euler polynomial, geometric degree comparison or native-rank formula.
