# Diagonal conjugation modulus on the adelic unipotent group

This internal supporting module computes the Haar character of conjugation by
an arbitrary diagonal point of the actual adelic general linear group. It assumes
a number field and compactness of its additive adelic quotient. If the diagonal
entries are the ideles d_i, the character is the product of |d_i/d_j| over i < j.

The implemented proof first identifies one-entry adelic rows with the additive
adeles. Pushing an additive Haar measure through evaluation transports the Haar
character of right multiplication by the one-entry diagonal matrix to that of
multiplication by the idele. The published `EqualAnalytic.rowModulus_eq_absDet`
then identifies this character with the existing idelic absolute value.

The `diagonalModulus` homomorphism packages this product as a positive unit.
It is defined without the compactness assumption. The coercion and nested
`Ioi` product lemmas expose its value for use in simple-root coordinates.

The conjugation theorem uses the published ranked triangular upper-entry coordinates
on the actual adelic unipotent group. Conjugation multiplies entry (i,j) by
d_i/d_j. The finite triangular Haar-character theorem and the scalar calculation
give the claimed product. This extends the previously published finite-place
torus calculation in `UnipotentConjugationModulus` to arbitrary diagonal ideles.
It asserts no Whittaker convergence estimate or quotient integration formula.
