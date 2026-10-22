# Polynomial division estimates for Weierstrass division

Author: Worker 56.

The file proves that division by a monic polynomial whose coefficients have
norm at most one does not increase the coefficient supremum norm of either
the quotient or the remainder. It works over any ultrametric normed
commutative ring. The final uniqueness statement assumes the ring is
nontrivial to express the strict remainder-degree bound. Completeness and
multiplicativity of the coefficient norm are not needed.

The implementation follows Mathlib's actual long-division recursion. Each
step subtracts the divisor times the leading-coefficient monomial. That
monomial has coefficients bounded by the input bound; the divisor's unit-ball
condition preserves this bound under multiplication, and the ultrametric
inequality preserves it under subtraction. The degree strictly decreases.
Induction bounds both recursive outputs, and the same inequality bounds the
updated quotient. Mathlib supplies the division equation, remainder degree
and uniqueness. No division, convergence or normalization result is assumed.

This is the finite polynomial estimate needed in the approximation proof of
Weierstrass division, in the retained Berkovich-course notes, section 2.2,
page 3. The displayed division theorem is printed as Proposition 2.1.1 and
subsequently referred to as 2.2.1. At unit radius, after normalizing the
distinguished leading coefficient to one, the polynomial truncation used in
that argument has coefficients of norm at most one. This file proves the
polynomial estimate only. The consuming modules use it for convergent
power-series division and preparation. Noether normalization uses those
analytic results in separate modules.

Original: undated notes of part of Vladimir Berkovich's course, Section 2,
*Affinoid algebras*, 14 pages, note-taker unidentified; PDF metadata dated
2011-02-28. Source ID
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
Retained file:
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`.
The full source was read and page 3 inspected visually.

All direct imports are Mathlib modules: polynomial coefficient supremum norm,
monic polynomial division and the ultrametric norm API. This helper supplies the finite estimates used by the analytic division proof.
