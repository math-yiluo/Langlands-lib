# Block-triangular matrices

Module: `Langlands.Global.SiegelFiniteness.BlockMatrices`. Provenance: internal; elementary
linear algebra used in the implemented proof of Siegel finiteness.

- `det_eq_zero_of_lowerLeft`: if a square matrix vanishes at all entries `(t, j)` with
  `j ≤ i ≤ t`, its determinant is zero. In the Leibniz expansion every permutation `σ` sends
  some column `c ≤ i` to a row `σ c ≥ i` (otherwise `σ` would inject the `i + 1` columns `≤ i`
  into the `i` rows `< i`), so every product has a zero factor.
- `exists_lowerLeft_ne_zero`: hence every invertible matrix over a field has, for each `i`, a
  nonzero entry `(t, j)` with `j ≤ i ≤ t`.
- `IsBlockUpper s M`: `M` vanishes in rows `≥ s`, columns `< s`.
  `isBlockUpper_of_isUpperTriangular` and `IsBlockUpper.mul` (closure under products).
- `unitary_row_sum`, `unitary_col_sum`: rows and columns of a unitary matrix over `RCLike 𝕜`
  have squared norms summing to `1`.
- `unitary_upperRight_eq_zero`: a unitary matrix with `IsBlockUpper s` vanishes in rows `< s`,
  columns `≥ s`. The first `s` rows have total squared mass `s`; the first `s` columns also
  have mass `s`, all of it in the first `s` rows; hence the upper-right block has mass zero.
