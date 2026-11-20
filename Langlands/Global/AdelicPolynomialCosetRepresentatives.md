# Polynomially bounded rational parabolic representatives

For a number field, a connected reductive group, a parabolic, and an exact
coordinate-line stabilizer representation of that parabolic,
`Langlands.Global.RepresentationGrowth.exists_polynomial_rationalCoset_representatives`
gives positive `C` and nonnegative `d` such that each rational parabolic
coset `c` has a rational representative whose lower-bounded adelic matrix
height is at most `C · H(c)^d`. Here `H(c)` is the multiplicative Weil height
of the inverse-orbit projective point in the prescribed representation.
The adelic matrix height can use any supplied matrix representation.

The proof uses the proper flag quotient with the prescribed line orbit as
its closed projective embedding. Finitely many basic-open sections cover
its rational points. `matrixAndInverseEntryFunction` pulls back the entry
or inverse-entry coordinate on the general linear group to a regular
function on the original group. Its evaluation at an identity-test
rational point is the corresponding matrix entry.

On each chart, the regular-function estimate bounds all the entry and
inverse-entry heights of the section lift by powers of the same
homogeneous projective height. The matrix height comparison combines these
estimates into a bound for the adelic height of that lift. Taking the
maximum exponent and a positive common coefficient over the finite cover
gives constants independent of the quotient point.

To handle the right-coset convention used in the Eisenstein series, the
proof applies the section to the quotient image of the inverse of an
initial rational representative and then inverts the lift. The exact
quotient fiber criterion proves equality of the rational cosets, and
inversion preserves the matrix-and-inverse height. The projective
orbit-coordinate formula identifies the homogeneous height with `H(c)`.

This internal proof supplies the representative bound used in the
compact-uniform moderate-growth argument. Its ingredients are the
published suite of algebraic quotient and opposite cell results and the
paired projective chart and scalar and matrix height estimates.
