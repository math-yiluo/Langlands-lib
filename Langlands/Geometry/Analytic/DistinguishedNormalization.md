# Leading-unit normalization of distinguished series

Author: Worker 56.

`IsDistinguished`, imported from `RestrictedSeriesDefinitions`, states
properties of the actual coefficient sequence:
the coefficient in degree `d` is a unit, its norm bounds every coefficient,
and all higher coefficients have strictly smaller norm. With multiplicative
coefficient norm, multiplication by that unit's inverse gives an actual
normalized distinguished series. The proof checks every coefficient bound
using multiplicativity and the unit identities.

The normalized division theorem gives a unique quotient and polynomial
remainder for any dividend. The product of the original divisor and its
quotient, as well as the remainder, has norm bounded by the dividend's norm.
Multiplication by the constant unit transports the quotient, and the
unrestricted sharp bounds for normalized division prove uniqueness.

The previously constructed normalized preparation also produces
unique unit and monic-polynomial factors for the original series. The
polynomial has degree `d` and coefficients of norm at most one. Both
existence and uniqueness are transported through multiplication by the
actual constant unit, without assuming any factorization.

The final instance packages the already proved Gauss multiplicativity for
`StrictTateAlgebra (Fin n) K`. Consequently the result applies with an
actual smaller Tate algebra as its coefficient ring. The separate
`TateRegrouping` module identifies this iterated algebra with the Tate
algebra on `n+1` variables.

This implements leading-unit normalization, the division theorem printed
as Proposition 2.1.1 on page 3 (later cited as 2.2.1), and Proposition 2.2.2 of the
retained Berkovich-course notes, Section 2.2, pages 2–4, at unit radius.
Coordinate changes, Noether normalization, and the spectral-polynomial
argument for general affinoid quotients are developed in separate modules.

Source `provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
