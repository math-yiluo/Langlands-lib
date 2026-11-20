# Transverse derivatives in real Levi coordinates

The lower block chart has value one at the zero coordinate and
derivative equal to the matrix of strictly lower off-block entries.
The signed orthogonal part at one therefore has derivative given
by extending these entries to a skew-symmetric matrix.

Multiply that orthogonal part by a positive diagonal matrix `D`,
then take the signed orthogonal part again. The resulting map is smooth
at zero. In its derivative each lower off-block entry is multiplied
by the ratio of the column diagonal of `D` to the row diagonal of `D`.
The other entries are determined by skew-symmetry.

The proof applies the derivative of the signed orthogonal part at one
and at the positive diagonal. Right multiplication by `D` multiplies
column `j` of the direction by `D j j`, and the second derivative
divides the lower entry in row `i` by `D i i`. Two real skew-symmetric
matrices with equal strictly lower entries are equal. This internal
calculation supplies the radial scaling in the fixed-flag derivative
of the compact trace argument.
