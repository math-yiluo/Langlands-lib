# Matrix identities for the unequal-rank projection

Provenance: internal. This module supports the proof of
`Langlands.Global.RankinSelbergGlobal.UnequalAnalyticStatement` (Cogdell 2004, Theorem 2.1).
It contains elementary matrix facts about the padding `padGL h M = diag(M, I)` and the
radical `Y_(n,k)` defined in `Langlands.Global.RankinSelberg.UnequalIntegrals`. The radical
is the Library block unipotent subgroup `blockUnipotentSubgroup A (projectionWeight n k)`,
which consists of the invertible matrices `y` with `y i j = 1 i j` whenever
`projectionWeight n k i ≤ projectionWeight n k j`. The weight
`projectionWeight n k i = -(i - k)` (natural subtraction) is `0` on the first `k + 1`
indices and then strictly decreasing. The analytic theory uses these facts as follows:

- the `k`-th column and the last row of an element of `Y_(n,k)` are standard basis vectors,
  which is the input of the decay estimate for the projection;
- the superdiagonal entries add, so the projection character is multiplicative;
- conjugating by a padded rational matrix `diag(γ, I)` maps `Y_(n,k)` to itself and does not
  change the superdiagonal, which gives left `GL_m(F)`-invariance of the projection.

All declarations are in the namespace `Langlands.Global.RankinSelbergGlobal.UnequalAnalytic`,
over an arbitrary commutative ring (`R` or `A`).

## Matrix products and padding

- `mul_apply_of_row`: if row `i` of `A` is the `i`-th standard basis row, then
  `(A * B) i j = B i j`. `mul_apply_of_col`: if column `j` of `B` is the `j`-th standard
  basis column, then `(A * B) i j = A i j`. Both expand `Matrix.mul_apply` and collapse the
  sum with `Finset.sum_ite_eq`.
- `padGL_apply` (**entries of `diag(M, I)`**): the `(i, j)` entry of `padGL h M` is
  `M ⟨i, _⟩ ⟨j, _⟩` if `i < m` and `j < m`, and `1 i j` otherwise. Proof: unfold the
  definition (the reindexed `fromBlocks M 0 0 1`), compute
  `finSumFinEquiv.symm` of the cast index (`Sum.inl` below `m`, `Sum.inr` from `m` on, two
  private lemmas), and treat the four blocks.
- `padGL_row`, `padGL_col`: rows and columns with index `≥ m` are standard basis rows and
  columns.
- `padGL_padGL`: padding from `m` to `k` and then to `n` is padding from `m` to `n`.
- `padGL_map`: padding commutes with applying a ring homomorphism to the entries
  (`Matrix.GeneralLinearGroup.map`).
- `det_padGL`: `det diag(M, I) = det M` (`Matrix.det_reindex_self`,
  `Matrix.det_fromBlocks_zero₂₁`).

## Weights

- `projectionWeight_nonpos`, `projectionWeight_eq_zero` (for `i ≤ k`),
  `projectionWeight_antitone`, and `projectionWeight_lt`: if
  `projectionWeight n k i < projectionWeight n k j` then `k < i`. All by `omega`.

## The radical `Y_(n,k)`

- `radical_col`: for `y ∈ Y_(n,k)`, the column with index `k` is the `k`-th standard basis
  column, since the weight there is `0`, the maximal value.
- `radical_row`: for `y ∈ Y_(n+1,k)`, the last row is the last standard basis row, since the
  last weight is minimal.
- `radical_upper`: elements of `Y_(n,k)` are upper triangular (the weight is antitone).
  `radical_det`: they have determinant `1` (`Matrix.det_of_isUpperTriangular`, diagonal
  entries `1`).
- `superdiag_mul`: for upper triangular matrices `N`, `P` with unit diagonal,
  `(N P) i (i+1) = N i (i+1) + P i (i+1)`. Only the terms `c = i` and `c = i + 1` survive in
  `Matrix.mul_apply`. `radical_superdiag_mul` is the same statement on `Y_(n+1,k)`.
- `radical_conj` (**the radical is normalized by the parabolic**): if `y ∈ Y_(n,k)` and `P`
  lies in the Library block parabolic `blockParabolicSubgroup A (projectionWeight n k)`, then
  `P⁻¹ y P ∈ Y_(n,k)`. Proof: the Library characterization `blockUnipotent_iff` (parabolic
  with block-diagonal part `1`) and the multiplicativity of the block-diagonal part on the
  parabolic (`blockDiagonalPart_mul`).
- `padGL_mem_parabolic`: `diag(M, I)` lies in that parabolic when `M` has size at most
  `k + 1`. The parabolic condition only concerns entries `(i, j)` with
  `projectionWeight i < projectionWeight j`, which forces `k < i`, and such rows of
  `diag(M, I)` are standard basis rows.
- `radical_superdiag_conj` (**conjugation fixes the superdiagonal**): if `M` has size
  `m ≤ k`, then `(diag(M, I)⁻¹ y diag(M, I)) i (i+1) = y i (i+1)` for `y ∈ Y_(n+1,k)`. Proof:
  if `i + 1 ≤ k`, both entries are `1 i (i+1) = 0` because the conjugate lies in `Y_(n+1,k)`
  (`radical_conj`) and the weights at `i` and `i + 1` are both `0`. Otherwise
  `i ≥ k ≥ m`, so row `i` of `diag(M, I)⁻¹ = diag(M⁻¹, I)` and column `i + 1` of `diag(M, I)`
  are standard basis vectors, and `mul_apply_of_row`, `mul_apply_of_col` remove both factors.
