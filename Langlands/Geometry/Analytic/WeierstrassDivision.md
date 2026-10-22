# Analytic division by a small perturbation of a monic polynomial

Author: Worker 56.

For a complete, nontrivial ultrametric normed commutative ring, this construction treats
a divisor which is a monic polynomial with unit-ball coefficients plus an
actual restricted series of norm strictly below one. Polynomial analytic
division is first used to define a quotient map. Its sharp norm bound on
differences makes the equation for the new quotient a contraction.
Mathlib's Banach fixed-point theorem constructs the solution.

The ultrametric inequality retains the sharp bounds for both quotient and
remainder. A positive norm cannot be at most a strictly smaller multiple of
itself; this proves the quotient bound and forces uniqueness of the
decomposition. Remainders are genuine polynomials of degree below the monic
polynomial. No division map or fixed point is assumed as output data.

This is the normalized analytic Weierstrass division argument in Section
2.2, page 3, of the retained Berkovich-course notes. The consuming modules
`DistinguishedSeries`, `WeierstrassPreparation` and
`DistinguishedNormalization` apply it to actual distinguished series.
Variable regrouping, coordinate changes and Noether normalization are
developed in separate modules.

Source `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
