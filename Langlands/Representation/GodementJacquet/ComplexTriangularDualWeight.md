# Diagonal weights in the dual matrix integral

The inverse transpose negates the logarithm of the normalized
determinant, so it negates the determinant exponent. In the dual
triangular expansion the diagonal coordinates of the inducing vector
are the inverses of the diagonal coordinates of the matrix test.
The strict entries are scaled by columns before transposition.

For a zero-based index `i` the column Jacobian contributes `−i`, the
inverted Borel half-modulus contributes `−r/2+i`, and the shifted
determinant contributes `s+r/2`. Their sum is `s`. The remaining
character on the `i`-th coordinate is `z ↦ χᵢ(z⁻¹)`.
