# The diagonal weights in the complex matrix zeta integral

In triangular coordinates the determinant modulus of the unitary factor
is one, as is the determinant of the upper unipotent factor. Thus the
determinant twist factors over the diagonal units.

For row \(i\) in zero-based indexing, the shift of the matrix zeta
parameter adds \((n-1)/2\), and the normalized principal-series
covariance adds \((n-1)/2-i\). The additive change of the strict upper
entries of that row contributes exponent \(-(n-1-i)\). With the
original determinant twist these sum to \(s\) at that diagonal
coordinate. `complexTriangular_zetaWeight` proves the resulting
identity for the exact normalization used by the Library.
