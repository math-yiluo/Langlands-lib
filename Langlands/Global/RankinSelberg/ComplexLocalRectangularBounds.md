# Iwasawa bounds for the complex rectangular kernel

`ComplexLocalRectangularBoundsStatement` concerns the exact three-block
chart with positive diagonal input \(\operatorname{diag}(\exp y_j)\)
and a rectangular matrix \(x\). Write \(z\) for the logarithmic Iwasawa
coordinate of the chart value, and put
\(X=\log(1+\sum_{i,j}\lVert x_{ij}\rVert^2)\).
The proposition bounds the sum of \(|z_i|\) by the large rank times
\(B+\sum_j |y_j|+X\). It also bounds \(\sum_j\max(y_j,0)+X\) by
\(K(1+\sum_i\max(z_i-z_{i+1},0))\), with nonnegative rank-dependent
constants \(B\) and \(K\).

The proof expresses the three-block chart as a two-block matrix with a
zero row appended to the rectangle. The final standard basis row makes
the last logarithm \(z_i\) zero. The simple-root sum then bounds every
\(z_i\) from above by telescoping. The rectangular trailing-minor
inequality bounds each rectangular entry in terms of the product of
the trailing Iwasawa diagonals, giving the bound for \(X\).

The triangular factor is the chart matrix times the inverse of its
unitary factor. Its inverse is the unitary factor times the explicit
inverse of the block matrix. Bounds for entries of these two products
control both signs of the Iwasawa logarithms. The inverse block formula
also isolates the factor \(\exp(-y_j)\) in each leading column. This
controls the positive input logarithms by the simple-root sum and \(X\).
The squared rectangular size equals the real trace of \(x x^*\), so it
is preserved by right multiplication by a unitary matrix.

These are logarithmic estimates derived from Jacquet 2009, §5.2,
pp. 33–35, especially the trailing-minor argument in Lemma 5.1 and its
use in Lemma 5.2. The bounds supply the geometric part of the rectangular
integrability argument.
