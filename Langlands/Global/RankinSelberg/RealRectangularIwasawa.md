# Toral Iwasawa coordinates of `[[g,0,0],[x,1,0],[0,0,1]]` over `ℝ`

Helper module for the convergence of the real unequal-rank dual block integral (towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`). Every declaration is proved, with no axioms beyond Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`).

All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealRectangularIwasawa`.

## The matrix

For `g ∈ GL_a(ℝ)` and a real `d × a` matrix `x`, `rect g x ∈ GL_(a+d+1)(ℝ)` is the Library's
`GeneralLinear.lowerBlockLocalization 1 g x 1`, the block matrix

`[[g, 0, 0], [x, 1_d, 0], [0, 0, 1]]`.

Its index set `Fin (a+d+1)` consists of the first block (`lowerBlockFirst`), the middle block
(`lowerBlockMiddle`) and the last index (`lowerBlockLast`).

- `sum_split`: a sum over `Fin (a+d+1)` is the sum over the three blocks.
- `rect_inv`: `(rect g x)⁻¹ = [[g⁻¹, 0, 0], [−x g⁻¹, 1, 0], [0, 0, 1]]`, from the Library's
  `lowerBlockLocalization_inv`.
- `rowsq_first`, `rowsq_middle`, `rowsq_last`: the squared Euclidean norms of the rows of
  `rect g x` are `∑_q g_(jq)²`, `∑_q x_(lq)² + 1` and `1`.
- `colsq_first`, `colsq_middle`, `colsq_last`: the squared norms of the columns of
  `(rect g x)⁻¹` are `∑_p ((g⁻¹)_(pj))² + ∑_l ((x g⁻¹)_(lj))²`, `1` and `1`.
- `gram_first`: the Gram matrix of the first `a` columns of `(rect g x)⁻¹` is
  `ᵗ(g⁻¹) (1 + ᵗx x) g⁻¹`.
- `exp_sum_first`: by `RealIwasawa.det_gram_inv_cols`,
  `exp(−2 ∑_(j<a) α_j(rect g x)) = det(g⁻¹)² det(1 + ᵗx x)`.

## Specialization to `g = torus y · k`

Let `y ∈ ℝ^a`, `k` orthogonal, and `z = zc y k x = α(rect (torus y · k) x)`. Write
`S = frob x = ∑_(l,p) x_(lp)²`.

- `torus_mul_apply`, `torus_mul_inv_apply`, `unitary_row_sq`, `rowsq_torus`, `colsq_torus`: the
  `j`-th row of `torus y · k` has squared norm `exp(2 y_j)`, and the `j`-th column of its inverse
  has squared norm `exp(−2 y_j)`.
- `sq_det_torus_mul_inv`: `det((torus y · k)⁻¹)² = exp(−2 ∑_j y_j)`.
- `sum_sq_mul_le`: the Cauchy–Schwarz inequality `∑_l (∑_p x_(lp) v_p)² ≤ S ∑_p v_p²`.

From the row and column bounds of `RealIwasawaBounds`:

- `first_upper`, `first_lower`: `y_j − log(1 + S)/2 ≤ z_j ≤ y_j` on the first block.
- `middle_upper`, `middle_lower`: `0 ≤ z_i ≤ log(1 + S)/2` on the middle block.
- `last_eq`: `z = 0` at the last index.
- `sum_first_le`: `∑_(j<a) z_j ≤ ∑_j y_j − log(1 + S)/2`. This uses `exp_sum_first`,
  `sq_det_torus_mul_inv` and `RealIwasawa.one_add_sum_sq_le_det`.
- `sum_all`: `∑_i z_i = ∑_j y_j`, by `RealIwasawa.log_abs_det_eq_sum_alpha` and
  `det(rect g x) = det g`.

The two estimates used for the gauge are:

- `sum_abs_le` (**growth**): `∑_i |z_i| ≤ ∑_j |y_j| + (a + d) log(1 + S)`.
- `decay_le` (**decay**):
  `∑_j max(y_j, 0) + a · log(1 + S)/2 ≤ (a + 2ad) · rootPos z`.
  Proof: since `z` vanishes at the last index, `RealConvergenceAnalysis.sub_last_le` gives
  `z_i ≤ rootPos z` for every `i`. On the first block this gives
  `max(y_j, 0) ≤ rootPos z + log(1 + S)/2`. On the middle block, `sum_all` and `sum_first_le`
  give `log(1 + S)/2 ≤ ∑_(middle) z_i ≤ d · rootPos z`. Adding the first estimate summed over
  `j` and `2a` times the second gives the claim.

## Relation to the literature

This is the real case of Jacquet's Lemma 5.2 (*Archimedean Rankin–Selberg integrals*, 2009,
p. 34), in the form needed for the gauge estimate: the Iwasawa torus of
`[[a, 0], [X, 1]]` controls both the torus `a` and the size of `X`. Jacquet derives it from
his Lemma 5.1 (p. 33) on exterior products. Here the coordinates are bounded through the row and
column bounds and one Gram determinant (module `RealIwasawaBounds`), and the decay is
expressed through the simple-root quantity `rootPos` of the module `RealConvergenceAnalysis`.
This arrangement was devised for the formalization.
