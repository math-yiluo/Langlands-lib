# Polynomial images under analytic power substitutions

Author: Worker 56.
Documentation correction: Worker 105, using Worker 291's audit analysis.

This file connects the actual power substitution to actual polynomials over
the smaller Tate algebra. Regrouping sends the pivot coordinate to the
polynomial variable and each remaining coordinate to a constant coefficient.
After the substitution, nonpivot coordinate `j + 1` becomes
`T^(b^(j + 1)) + X j`. The definition `shearPolynomial` permits every natural
base `b`. When `0 < b`, `shearPolynomial_monic` proves that each coordinate
polynomial is monic. Under the same hypothesis, `shearMonomialPolynomial_monic`
and `shearMonomialPolynomial_natDegree` prove that the product assigned to a
monomial exponent is monic and has degree equal to that exponent's base-power
weight. The single-coordinate theorem `shearPolynomial_natDegree` is
unconditional: its `natDegree` is `b^i` for every natural `b`.

The positive-base restriction matters for monicity. For `n = 1`, `b = 0`,
and nonpivot coordinate `i = 1`, the outer polynomial is `C(1 + X 0)`.
Over a normed field, the coefficient `1 + X 0` is neither zero nor one, as
seen from its constant and degree-one coefficients in the smaller Tate
algebra. Thus this constant outer polynomial is not monic; taking exponent
one at this coordinate alone gives the same counterexample for the product.

In the distinguished-coordinate application, `separatingBase S` is at least
two by `separatingBase_two_le`. The proof of
`exists_distinguished_coordinateChange` in `TateDistinguishedCoordinates`
explicitly derives `0 < b` from this bound and supplies it to the polynomial
lemmas. The actual analytic application therefore satisfies the required
hypothesis.

The images of scalar monomials are proved equal to these polynomials through
the genuine evaluation and regrouping maps. No polynomial representative of an
analytic image is taken as an assumption.

Source: retained Berkovich-course notes, Section 2.2, Proposition 2.2.5, page
4; coordinate zero is the pivot instead of the notes' last coordinate. The
finite dominant-sum and small-perturbation steps are assembled in the
subsequent `TateDistinguishedCoordinates` module.

Source
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
