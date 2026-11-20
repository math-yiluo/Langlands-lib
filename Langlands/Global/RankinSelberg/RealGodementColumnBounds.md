# Iwasawa bounds for the real Godement first-column integral

Write `y` for the logarithmic Iwasawa coordinate of the lower Whittaker representative `w_m h⁻¹`. The sum of these coordinates is `-log |det h|`. The sum of their absolute values is bounded by `m` times the sum of the logarithmic norms of the two Fourier arguments and the positive simple-root sum. The norm factors inside the logarithms are `m (1 + ‖h‖)` and `m (1 + ‖h⁻ᵀ e₀‖)`, using the Euclidean norms of matrix and column entries.

The inverse of the triangular Iwasawa factor has diagonal entries `exp(-y_i)`. Expressing it as the orthogonal factor times `h w_m` bounds each such entry by `m ‖h‖`. The last row of `w_m h⁻¹` is the first row of `h⁻¹`, which is the first-column Fourier frequency written as a row. Multiplication by the inverse orthogonal factor bounds `exp(y_last)` by `m ‖h⁻ᵀ e₀‖`. The simple-root inequality bounds each `y_i` from above by `y_last` plus the positive simple-root sum. Taking logarithms, bounding both signs of each coordinate, and summing gives the claimed estimate.

These are real upper-Borel bounds for the convergence argument in Hervé Jacquet, *Archimedean Rankin–Selberg Integrals*, Section 7.2, Proposition 7.2.
