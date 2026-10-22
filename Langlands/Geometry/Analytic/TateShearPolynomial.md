# Polynomial images under analytic power substitutions

Author: Worker 56.

This file connects the actual power substitution to actual polynomials over
the smaller Tate algebra. Regrouping sends the pivot coordinate to the
polynomial variable and each remaining coordinate to a constant coefficient.
After the substitution, a nonpivot coordinate becomes `T^(b^i) + X i`. Its
polynomial is monic, and the product assigned to a monomial exponent is monic
of degree equal to that exponent's base-power weight.

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
