# Block matrices of shape `(1, m)`

Author: Worker 392.

This helper module of the proof of
`Langlands.Conductor.OrderedUnramifiedSphericalCyclicityStatement` (see
[`OrderedUnramifiedSphericalCyclicity`](../OrderedUnramifiedSphericalCyclicity.md))
supplies elementary block-matrix bookkeeping over an arbitrary ring. It imports only
Mathlib. All declarations are in `Langlands.Conductor.SphericalCyclicity` and are
internal auxiliary definitions, with no literature source.

## Definitions

For a matrix `X` of size `m + 1`, indexed by `Fin (m + 1)`:

- `blk a r c D` is the block matrix `[[a, r], [c, D]]` with `a : R`,
  `r c : Fin m → R` and `D : Matrix (Fin m) (Fin m) R`. It is built with `Fin.cons`.
  The simp lemmas `blk_zero_zero`, `blk_zero_succ`, `blk_succ_zero` and
  `blk_succ_succ` evaluate its entries.
- `rowT X j = X 0 (j+1)` is the tail of the first row, `colT X i = X (i+1) 0` is the
  tail of the first column, and `low X = X.submatrix succ succ` is the lower-right
  `m × m` block.
- `blockDiag α h`, for a unit `α` and `h : GL (Fin m) R`, is the invertible matrix
  `diag(α, h) = blk α 0 0 h`. Its inverse is `blk α⁻¹ 0 0 h⁻¹`.
- `lowerUnip y`, for `y : Fin m → R`, is the invertible lower unipotent matrix
  `blk 1 0 y 1`. Its inverse is `blk 1 0 (-y) 1`.

## Results

- `blk_eta`: `blk (X 0 0) (rowT X) (colT X) (low X) = X`, and `blk_ext`: two matrices
  with the same four blocks are equal. Both are proved by `Fin.cases` on both
  indices.
- Over a commutative ring, `mul_zero_zero`, `rowT_mul`, `colT_mul`, `low_mul` and
  `blk_mul` give the block form of a product:
  `(X Y)₀₀ = X₀₀ Y₀₀ + rowT X ⬝ colT Y`,
  `rowT (X Y) = X₀₀ • rowT Y + rowT X ᵥ* low Y`,
  `colT (X Y) = Y₀₀ • colT X + low X *ᵥ colT Y`, and
  `low (X Y) = vecMulVec (colT X) (rowT Y) + low X * low Y`.
  Each is proved by expanding `Matrix.mul_apply` with `Fin.sum_univ_succ`.
- `det_of_colT_eq_zero`: if `colT X = 0` then `det X = X₀₀ * det (low X)`. This is
  Laplace expansion along column zero (`Matrix.det_succ_column_zero`): every term
  except the first vanishes. `det_blk_zero` is the special case `blk a r 0 D`.
- `blk_one`: `blk 1 0 0 1 = 1`.
- `blockDiag_val` and `blockDiag_mul`:
  `diag(α, h) diag(β, k) = diag(αβ, hk)`.
- `lowerUnip_val`, `lowerUnip_add` (`L(y) L(y') = L(y + y')`), `lowerUnip_zero`,
  `lowerUnip_inv` (`L(y)⁻¹ = L(-y)`), and `det_lowerUnip` (`det L(y) = 1`, by
  expansion along row zero).
