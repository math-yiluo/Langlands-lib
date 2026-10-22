# Triangular coordinate changes on actual Tate algebras

Author: Worker 56.

For a complete ultrametric normed field, the construction sends each
coordinate `X i` to `X i + c i * (X p)^(e i)`, where `p` is a fixed pivot, `c
p = 0`, and every scalar coefficient has norm at most one. The actual
convergent evaluation homomorphism constructs the substitution. Negating the
scalar coefficients constructs its inverse. The bounded universal property
verifies the inverse identities on the generators. Both maps are contractive,
and therefore the resulting algebra automorphism is an isometry.

This is the coordinate-substitution part of the argument in the retained
Berkovich-course notes, Section 2.2, Proposition 2.2.5, page 4. The notes use
the last coordinate and suitable integral powers. The implementation allows
any pivot and any exponents. The subsequent `TateDistinguishedCoordinates`
module constructs exponents that make a given nonzero series distinguished. No
distinguished output, normalization, or spectral-bound conclusion is assumed
by this construction.

Source
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
