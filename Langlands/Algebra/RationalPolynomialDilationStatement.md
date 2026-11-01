# Uniqueness and dilation of rational polynomials

`Langlands.Algebra.RationalPolynomialDilationStatement` collects four
arithmetic assertions for ordinary polynomials over the rational numbers.

1. If two rational polynomials agree at every sufficiently large natural
   number, they are equal.
2. If `Q(n) = P(q*n)` at every sufficiently large natural number, where `q`
   is natural, then `Q = P.comp (C q * X)`.
3. For positive natural `q`, the polynomial `P.comp (C q * X)` has the same
   natural degree as `P`, and its leading coefficient is the leading
   coefficient of `P` multiplied by `q ^ P.natDegree`.
4. Suppose `P` is nonzero with natural degree `g`, `q` is positive, and the
   eventual evaluation relation in the second assertion holds. If the
   leading coefficient of `Q` is `r` times the leading coefficient of `P`,
   for a natural number `r`, then `r = q ^ g`.

All coefficients and evaluations in these comparisons lie in `ℚ`; `q`, `r`
and `g` are natural numbers. Eventual equality refers to the natural-number
filter `atTop`. Equality at every natural number therefore suffices. The
degree and cancellation assertions include `q = 1` and `g = 0`. The second
assertion also allows `q = 0`; the third assertion allows the zero
polynomial.

This is an internal arithmetic interface derived from Mathlib's finite
root bound, polynomial composition and its coefficient formula. The
infinitely many distinct rational images of a natural-number tail give
uniqueness. Dilation multiplies coefficient number `i` by `q ^ i`, and
nonzero leading-coefficient cancellation gives the last assertion.

The intended application is the final polynomial calculation in the
polarized finite-flat rank argument. This interface contains no schemes,
line bundles or native ranks. Establishing actual Euler polynomials, their
degrees, and the geometric leading-coefficient comparison remains a
separate obligation. This file states the arithmetic interface only.
