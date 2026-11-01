# Diagonal Iwasawa density and block modulus

This internal package derives geometric bounds for the explicit normalized
characters already present in the fixed-slice convergence problem.

`diagonalDensity` is the inverse product of normalized absolute values of
all positive diagonal-root ratios, evaluated on canonical uniformizer powers.
Each inverse ratio is `q` to the difference of its two integer exponents,
and is at most `q ^ (2 * torusSize lam)`. Bounding each filtered product by
the product over all coordinates gives
`diagonalDensity F lam ≤ (q ^ (2 * n * n)) ^ torusSize lam`.
The estimate is deliberately coarse and independent of every real twist.

`determinantNorm_torus` computes the exact determinant norm as `q` to
the negative sum of the diagonal exponents. It follows from the diagonal
determinant formula, multiplicativity of normalized absolute value and the
uniformizer formula. If every exponent lies between `-e` and `e`, both the
determinant norm and its inverse are at most `q ^ (n * e)`.

`torusLevi` extracts the two uniformizer diagonal blocks. Each is entry
bounded by the full `torusSize`. For these blocks, the norm of the inverse
upper half modulus is the square root of the inverse full modulus.
The full modulus is the first block determinant norm to the second rank,
divided by the second determinant norm to the first rank. Applying the
two determinant bounds and taking a square root gives
`(q ^ ((m 0 + 1) * (m 1 + 1))) ^ torusSize lam`.

These results are elementary consequences of the published explicit
modulus and canonical uniformizer definitions. They supply pointwise growth
bases for a later summable majorant and assert no outer integral convergence.
