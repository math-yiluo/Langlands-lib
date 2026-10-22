# Finiteness from distinguished-series division

Author: Worker 56.

Let `A` be a complete ultrametric normed commutative ring with nonzero unit,
unit norm one, and multiplicative norm. If a surjective `A`-algebra map out of
the actual restricted-series algebra kills a distinguished series of degree
`d`, the proof constructs a surjective linear map from the module of
polynomials of degree less than `d`. For a target element, take a preimage and
apply the already proved analytic division theorem. Its polynomial remainder
maps to the original element because the divisor maps to zero.

Mathlib's explicit basis `1, X, ..., X^(d-1)` for the low-degree polynomial
module supplies finite generation of the target. Degree zero is included: the
source of this surjection is then the zero module. The target need not carry a
norm or topology.

The ring-map version derives the coefficient action by restriction to constant
series. The quotient version applies the theorem to the actual quotient map of
any ideal containing the distinguished series. It needs no closedness
hypothesis, because the conclusion here is algebraic module finiteness, not a
statement about a quotient Banach topology.

For an actual finite ring map that need not be surjective, the final theorem
factors it through the principal-ideal quotient of the killed distinguished
series. The quotient is finite by the preceding construction. The original
finite-module structure descends to the factor map, and transitivity of finite
modules proves finiteness over the coefficients.

This is the finite-module consequence of Weierstrass division in the retained
Berkovich-course notes, Section 2.2, Proposition 2.2.4, page 4. Division is
proved in the preceding modules, not supplied as an assumption.

Source
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
