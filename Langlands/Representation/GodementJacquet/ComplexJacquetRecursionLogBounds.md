# Iwasawa logarithms in the last-column recursion

These internal estimates support Jacquet's single-group integral in §7.3,
equation (7.7), of *Archimedean Rankin–Selberg Integrals* (2009). They use
the group's inverse matrix as the first block of the partially transformed
test function and its last row as the last-column Fourier frequency.

For `k = u expDiagonal(x) v`, the unitary matrix `v` brings `k⁻¹` to
`expDiagonal(-x) u⁻¹`. Its diagonal entries bound every `exp(-xᵢ)` by the
dimension times the entrywise norm of `k⁻¹`. Multiplying `k` by `v⁻¹` and
taking the last diagonal entry bounds `exp(x_last)` by the dimension times
the norm of the last row of `k`. The bounds use the entrywise estimate
`|vᵢⱼ| ≤ 1` for a unitary matrix.

The positive parts of the logarithmic simple-root ratios bound the
difference between any `xᵢ` and `x_last` by telescoping. Summing the resulting
coordinate estimates bounds the sum of absolute logarithms by the two
logarithmic matrix and row bounds plus the simple-root sum, with a dimension
factor. The determinant modulus of `k⁻¹` is `exp(-2 ∑ᵢ xᵢ)` because the
unipotent and unitary factors have determinant modulus one.

For a coefficient with unipotent-invariant norm and the simple-root bound,
the last theorem absorbs any fixed normalized determinant exponent into
the common logarithmic growth exponent. It chooses a natural decay order
at least the enlarged exponent times the dimension. The simple-root term
then cancels and the estimate becomes polynomial in the inverse matrix
norm and the last-row norm, with the same power for both.
