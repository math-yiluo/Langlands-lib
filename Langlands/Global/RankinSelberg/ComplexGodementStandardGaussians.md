# Standard polynomial Gaussians for the split complex Godement integral

Dilation of the matrix argument by the positive square root of `2π` turns the scale-one rectangular Gaussian into the standard Gaussian. It substitutes a scalar multiple for each real polynomial coordinate and gives a square polynomial Gaussian when the matrix is square. Identifying a single column with its vector yields a polynomial Gaussian of the same scale on the row space.

`ComplexGodementStandardGaussianSplitStatement` applies this dilation to the existing column decomposition. The dilation acts on the leading square block and the last column separately, so both factors in each summand are standard polynomial Gaussians.

These are derived test identities for Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), p. 10 and Proposition 8.1, author-posted pp. 60–61.
