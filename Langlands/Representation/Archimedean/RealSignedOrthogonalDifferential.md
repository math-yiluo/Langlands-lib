# Differential of the signed orthogonal part

The signed orthogonal part is the matrix defined by the Gram-column
formula for the principal series. It is smooth at every invertible
matrix, where the Gram determinants are positive.

At a positive diagonal matrix `D`, its value is `1`. Its derivative
in a direction `H` is skew-symmetric, and its lower entry at `i, j`
for `j < i` is `H i j / D i i`.

The proof differentiates the orthogonality identity near `D` to obtain
skew-symmetry. It also differentiates the vanishing lower entries of
the product of a matrix with the transpose of its signed orthogonal
part. This product is upper triangular by the triangular–orthogonal
factorization and the signed Gram formula. The lower entry of its
derivative is the lower entry of `H` minus the derivative entry
multiplied by the corresponding positive diagonal entry of `D`.

This internal calculation gives the transverse derivative needed
near a fixed block flag in the compact trace integral.
