# Determinant normalization of the rectangular gauge weight

This internal module defines `HasLastStandardRow`, the property that a
matrix's last row is the last standard basis row.

For a supplied upper-unipotent, diagonal, standard-compact
factorization of such an adelic matrix, its final diagonal idele is
the corresponding diagonal entry of the inverse compact factor.
The proof multiplies by the inverse compact factor and expands that
entry. The finite value is therefore integral, and its mixed
archimedean norm is at most one by orthogonality or unitarity. The
full-idele norm estimate from `IdeleDenominatorNorm` makes its full
absolute value at most one. The actual three-block rectangular chart
has the required last row by the published block formulas.

The determinant/root identity states that the product of a diagonal
tuple equals its last entry to the ambient rank times the product
of its adjacent roots to powers `1,2,...,r`. The proof reuses the
published block-root determinant identity and splits off its final
coordinate, then applies the full idele norm.

For `τ ≥ 0`, multiplying the gauge's diagonal weight by the determinant
norm to power `τ` leaves a factor of the last diagonal norm to
power `(r+1)*τ` and root weights with exponents `i*τ`. The last factor
is at most one under the last-row hypothesis, so the normalized
weight is bounded by the product of these nonnegative root powers.
The implemented proof reuses the fixed-root scalar-power identity,
positivity of idelic norms and the monotonicity of real powers.

This normalization will allow fixed root powers to be absorbed by
Schwartz decay and shift the final determinant exponent by `τ`. The
module itself proves only the displayed identities and inequalities,
not that absorption or Mellin convergence.
