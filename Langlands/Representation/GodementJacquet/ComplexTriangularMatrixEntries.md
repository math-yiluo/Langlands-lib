# Additive entries of the upper triangular matrix

In diagonal-then-unipotent coordinates, the strict upper entry in row
\(i\) is scaled by the diagonal unit \(d_i\). The theorem
`integral_diagonal_mul_upperEntries` performs this change of variables
on the product of the supplied additive scalar Haar measures. The
factor is the inverse product of the normalized absolute values of
the scaling coordinates.

`prod_complexUpperEntryScale` rewrites that product row by row. The
fiber over \(i\) is identified with the positions strictly to the
right of \(i\), so the exponent for \(d_i\) is \(n-1-i\) in
zero-based indexing. This is the change of variables needed to cancel
the standard-module normalization in the matrix zeta integral.
The analogous right-diagonal multiplication scales each strict entry
by its column diagonal. The same product-measure change of variables
computes its Jacobian. There are `j` strict upper entries in the
zero-based column `j`, so the column determinant factor is
`∏ⱼ |dⱼ|_ℂ^(-j)`. This is used after transpose in the dual integral.
