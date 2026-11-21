# Compact polynomial multiplication in a real standard module

`RealStandardCompactMultiplierStatement` starts with an `O(n)`-finite
standard vector and a continuous polynomial function on `O(n)`. The
polynomial is invariant under left multiplication by diagonal sign
matrices and by rotations within each inducing block. The proposition
constructs a standard vector that restricts on `O(n)` to the product of
the two compact functions.

The proof `realStandardCompactMultiplier` first expresses the compact
restriction of the input vector as a polynomial in matrix entries. The
product is again polynomial, so its right translates span a
finite-dimensional space. Its sign covariance follows from the sign
covariance of the original vector and left invariance of the multiplier.
The Library's `principalSeriesExtension` supplies the normalized
principal-series extension. The polynomial is constant on every left
block-rotation orbit. It therefore factors out of the block Fourier
coefficients on the compact group. The original coefficients vanish in
the required windows, so the extension belongs to the standard module.

This internal lemma uses the Library's compact polynomial, extension and
block Fourier APIs. It permits polynomial localization inside the
algebraic space of compact-finite vectors.
