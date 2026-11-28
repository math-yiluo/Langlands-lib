# Lower-right corner minors of orthogonal matrices

Module `Langlands.Global.RankinSelberg.RealCompactDiracCorner`, namespace
`Langlands.Global.RankinSelbergGlobal.RealCompactDirac`.

Linear algebra on the big cell `B N̄` of `GL_n(ℝ)`, used in the proof of
`RealStandardCompactDiracStatement` (module `RealStandardCompactDiracProof`). Minors are the
Library's `MatrixMinor.minor X A B` (rows `A`, columns `B`, both in increasing order).

## Definitions

* `tail n l : Finset (Fin n)`: the positions `l, …, n - 1` (`mem_tail`). It is a bottom
  segment in the sense of `RealTiedMinorProduct.IsBottom` (`isBottom_tail`); `tail n 0` is
  everything and `tail n l` is empty for `l ≥ n`.
* `corner X l = minor X (tail n l) (tail n l)`: the lower-right corner minor of size `n - l`.
  `corner X 0 = det X` and `corner X l = 1` for `l ≥ n`.
* `addColumn j i = 1 + E_{ji}`: right multiplication by it adds column `j` to column `i`
  (`mul_addColumn_apply`).
* `lowerConstant n = 1 + n! 2ⁿ`.

## Results

* `corner_upper_mul`, `corner_diagonal_mul`: for `b` upper triangular,
  `corner (b X) l = (∏_{i ≥ l} b_ii) · corner X l` (from the Library's
  `RealTiedMinorProduct.minor_upper_mul`), and the same for diagonal `b`
  (`MatrixMinor.minor_diagonal_mul`).
* `corner_of_isLowerUnipotent`: corner minors of a lower unipotent matrix are `1`.
* `corner_eq_prod`, `corner_eq_mul_succ`: if `X = b L` with `b` upper triangular and `L` lower
  unipotent, then `corner X l = ∏_{i ≥ l} b_ii`, hence `corner X l = b_ll · corner X (l + 1)`.
* `sum_minor_sq`, `abs_minor_le_one`, `abs_corner_le_one`: for `X Xᵀ = 1`, the squares of the
  minors of `X` with a fixed row set `A` sum to `1`, so every minor with `|A| = |B|` has absolute
  value at most `1`. Proof: Cauchy–Binet (`MatrixMinor.minor_mul`) for `X Xᵀ = 1`, with
  `minor Xᵀ C A = minor X A C` and `minor 1 A A = 1`.
* `cornerNonzero_of_corner_ne_zero`: nonzero corner minors give the Library's recursive
  `LowerUnipotentRestriction.CornerNonzero`. The corner minors of `X.submatrix succ succ` are
  those of `X` shifted by one (`corner_submatrix_succ`, via
  `MatrixMinor.minor_submatrix_orderEmb` and `tail_map_succ`).
* `abs_entry_le_one`: entries of an orthogonal matrix have absolute value at most `1`.
* `abs_minor_le_of_entry_le_two`: every principal minor `minor Y A A` of a matrix `Y` with
  entries bounded by `2` is bounded by `n! 2ⁿ` (Mathlib's `Matrix.det_le`).
* `abs_lower_entry_le` (**the lower unipotent factor on the big cell**): if `X Xᵀ = 1`,
  `X = b L` with `b` upper triangular and `L` lower unipotent, `j < i` and `corner X i ≠ 0`,
  then `|L i j| ≤ lowerConstant n / |corner X i|`.

## Proof of `abs_lower_entry_le`

`corner_lower_mul_addColumn`: for lower unipotent `L` and `j < i`, the corner minor at `i` of
`L (1 + E_{ji})` is `1 + L i j`. Indeed on the rows `≥ i` the matrix `L (1 + E_{ji})` agrees
with a lower triangular matrix whose diagonal entries are `1 + L i j` at `i` and `1` after it
(`MatrixMinor.minor_congr`, `MatrixMinor.minor_of_isLowerTriangular`). Multiplying by `b` on
the left, `corner (X (1 + E_{ji})) i = corner X i · (1 + L i j)`. The entries of
`X (1 + E_{ji})` are bounded by `2`, so `|corner X i| |1 + L i j| ≤ n! 2ⁿ`. With
`|corner X i| ≤ 1` this gives `|L i j| ≤ |1 + L i j| + 1 ≤ (n! 2ⁿ + 1) / |corner X i|`.

## Provenance

Derived, internal infrastructure; no literature source is claimed. The statements are standard
facts about the `LU` decomposition on the big cell. The entry of `L` is, up to the factor
`corner X i`, a minor of `X`; the module bounds it through the minor of `X (1 + E_{ji})`
instead of computing that minor.
