# Height bound for real principal-series vectors

For the position principal series of a fixed list of real blocks and a
positive matrix size, `RealPrincipalSeriesHeightStatement` bounds each vector
by its compact supremum times a common polynomial in the matrix height.
The height is the sum of the squared entries of the matrix and its inverse.
The natural exponent and the comparison constant depend on the inducing
data and the size. The bound holds for every smooth vector of the principal
series.

Write the matrix in Iwasawa form `diag(d) u k`. The squared diagonal entries
of the triangular factor are bounded by the squared Frobenius norm of the
matrix. The inverse matrix contains the inverse triangular factor, whose
diagonal entries are `dᵢ⁻¹`. Orthogonal multiplication leaves the Frobenius
norm unchanged, so the height bounds both `|dᵢ|` and `|dᵢ|⁻¹`. This bounds
the absolute value of each diagonal logarithm by the logarithm of the height.

The established estimate for the principal-series character uses the sum
of the absolute real parts of the shifted exponents. Taking the natural
ceiling gives a common polynomial power. Principal-series equivariance
multiplies this estimate by the compact bound for the vector.

Left multiplication by an orthogonal matrix preserves the height. Right
derivatives preserve the smooth principal series, and each derivative
word of a vector has a finite bound on the compact subgroup. Applying
the same character estimate to every word gives a single exponent for
all vectors and all words, with a constant for each vector and word.

This is a Library-specific bound for the inducing model used in Jacquet's
real principal-series reduction. It provides one estimate for studying
continuous Whittaker functionals on that model. The coefficient-space
extension needed in §11 remains a separate step. [Jacquet, *Archimedean Rankin–Selberg Integrals*, §11, pp. 81–82](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
