# Rotated diagonal coordinates for the lower quotient

This internal package records the coordinate calculations used to combine the
published block-section growth estimate with the standard quotient Iwasawa
coordinates. `rotatedExponents h lam` composes the standard exponent vector with
the inverse block-reversing permutation. The permutation preserves `torusSize`.
At the cut `j.val = m 1`, the signed degree on `Iic j.castSucc` is the sum in
the second original block minus the sum in the first original block.

Reassembling the two diagonal blocks extracted by `torusLevi` gives the original
torus. Applying the exact determinant norm formula to the rotated blocks proves
that their opposing determinant powers are exactly `q ^ (-u * twistDegree)`.
These are derived consequences of the published permutation-coordinate laws,
diagonal embedding and determinant formulas. No integrability is asserted.
