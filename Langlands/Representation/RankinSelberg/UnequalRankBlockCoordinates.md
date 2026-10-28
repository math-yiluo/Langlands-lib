# Block coordinates for the unequal-rank block-zero covariance laws

Authors: Worker 822 (Lean) and Worker 233 (Markdown). Part of the proof task
`4564f536-d9dc-4d9a-aeb5-4ee980417bd3` for the published statement
`Langlands.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement`; its
consumers are `UnequalRankBlockZeroCovariance` and
`UnequalRankBlockZeroContinuedFormsProof`.

This module contains only matrix algebra over an arbitrary field `F` (no
topology, measure or representation). The indices `Fin N` of `GL_N` are split
as `Fin (n + 1) ⊕ Fin m`: the leading block of size `n + 1` followed by the
remaining `m` indices. In these coordinates the Library's embedding
`appendIdentity`, the JPSS matrix `unequalRankMatrix`, the block Weyl element
`blockWeylAt` and the elements of `U_(n+2,r+1)`
(`IsUnequalRankCovarianceUnipotent`) become ordinary `Matrix.fromBlocks`
matrices. The two matrix identities behind JPSS (2.11.4), one for each of the
two integrals, are then proved by block multiplication. Nothing published is
redefined. The module defines only the coordinate change `blockCoords`, the
block reading `blockForm` and the row padding `stackRows`.

Notation below: `[P, Q; R, S]` is `Matrix.fromBlocks P Q R S`, `w_m` is
`weylLong m F`, `g⁻ᵀ` is `inverseTranspose`, and `Σ M` is the first
superdiagonal sum `∑ i : Fin r, M i.castSucc i.succ` that the Library's
`standardCharacter ψ r` evaluates.

## Coordinates

- `blockCoords h : Fin (n + 1) ⊕ Fin m ≃ Fin N` for `h : n + 1 + m = N` is
  `finSumFinEquiv` followed by `finCongr h`. `blockCoords_inl_val` and
  `blockCoords_inr_val` (both `rfl`, simp lemmas) give the values `a` and
  `n + 1 + b`. `blockCoords_symm_of_lt` and `blockCoords_symm_of_le` compute the
  inverse on indices `< n + 1` and `≥ n + 1`.
- `blockForm h M` is `M.submatrix (blockCoords h) (blockCoords h)`.
  `blockForm_apply` (`rfl`) and `entry_eq_blockForm` read entries through it.
- `blockForm` is compatible with the ring structure and transposition:
  `blockForm_mul`, `blockForm_one`, `blockForm_add`, `blockForm_transpose`. It
  is injective (`blockForm_injective`), so two elements of `GL_N(F)` with equal
  block forms are equal (`generalLinear_ext_blockForm`). All later identities
  in `GL_N(F)` are proved this way.
- `upperUnitriangular_of_blockForm`: if `blockForm h M = [P, Q; 0, S]` with
  `P` and `S` upper triangular with unit diagonal, then `M` is upper triangular
  with unit diagonal.

## The specific block matrices

- `blockForm_of_diagEntries`: a matrix whose entries are those of `diag(g, I)`
  (the entry formula of `appendIdentity_entry`) has block form `[g, 0; 0, 1]`.
  Consequences: `blockForm_appendIdentity` for `appendIdentity n m g`, and
  `blockForm_embedding` for the reindexed embedding
  `GeneralLinear.reindex (finCongr _) (appendIdentity n (r - n) g)` that the
  published predicate `IsUnequalRankBilinearCovariant` uses, whenever
  `n + 1 + m = r + 1`.
- `reindex_appendIdentity_eq`: when `r = n + m` literally, the reindexed
  embedding is `appendIdentity n m g` itself. The Covariance module uses it to
  pass between the two forms after `subst`.
- `stackRows m x` is the matrix with `m` rows whose row `i` is row `i` of
  `x : Matrix (Fin j) (Fin (n + 1)) F` for `i < j` and zero otherwise (here
  always `j ≤ m`: the rows of `x` followed by zero rows).
  `blockForm_rectangularEntries` gives
  `blockForm (rectangularEntries j k x) = [0, 0; stackRows (j+k+1) x, 0]`, and
  hence `blockForm_unequalRankMatrix`: the JPSS matrix
  `unequalRankMatrix j k g x` has block form `[g, 0; stackRows (j+k+1) x, 1]`.
- `blockForm_blockWeylAt`: `blockWeylAt n r hnr` has block form
  `[1, 0; 0, w_m]` when `n + 1 + m = r + 1`. `blockForm_reindex_blockSum`:
  the reindexed `blockSum (g₁, g₂)` has block form `[g₁, 0; 0, g₂]`.

## Upper unipotent matrices in block form

- `toBlocks₂₁_blockForm_of_upper`: the lower-left block of an upper
  triangular matrix is zero. `toBlocks₂₂_blockForm_lower_zero`: its lower-right
  block is upper triangular. `blockForm_upperUnipotent`: hence every
  `u : upperUnipotent (r + 1) F` has block form `[u₁₁, u₁₂; 0, u₂₂]`.
- `toBlocks₁₁_covarianceUnipotent`: for `u ∈ U_(n+2,r+1)` the leading
  `(n+1)`-block is the identity. `toBlocks₁₂_covarianceUnipotent_zero`: when
  the second summand is written `Fin (m + 1)`, the first column of the
  upper-right block vanishes. Both follow from the published predicate, whose
  leading `(n+2)`-square block is the identity.
- `superdiag_sum_blockForm` splits `Σ M` in coordinates `(n+1) + (m+1)` as the
  superdiagonal of the leading block, plus the corner entry in row `n` and
  column `n + 1`, plus the superdiagonal of the trailing block.
  `superdiag_sum_of_blockForm`: if `blockForm M = [1, Q; 0, S]` and the first
  column of `Q` vanishes, then `Σ M = Σ S`.
- `covarianceUnipotent_blocks`: for `u ∈ U_(n+2,r+1)`, the matrices `u` and
  `u⁻¹` have block forms `[1, Q; 0, D]` and `[1, Q'; 0, D']` with
  `D D' = D' D = 1`. Here `u⁻¹ ∈ U_(n+2,r+1)` because the Library's
  `unequalRankCovarianceSubgroup` is a subgroup.

## Identities

- `stackRows_mul`: `stackRows m x * g = stackRows m (x * g)`.
- `unequalRankMatrix_mul_appendIdentity`: right translation by `diag(g, I)`
  acts on both JPSS variables,
  `M_(j,k)(a, x) · diag(g, I) = M_(j,k)(a g, x g)`.
- `inverseTranspose_embedding`: the reindexed embedding commutes with the
  inverse transpose, `ι(g)⁻ᵀ = ι(g⁻ᵀ)`. `blockWeylAt_mul_embedding`:
  `w_B · ι(g) = ι(g) · w_B` for `w_B = blockWeylAt n r hnr`. Both are block
  computations with `[g, 0; 0, 1]` and `[1, 0; 0, w_m]`.
- `weylLong_mul_apply`: left multiplication by `w_m` reverses the rows,
  `(w_m M) i b = M (rev i) b`.
- `originalUnipotent_identity` (JPSS (2.11.4) for the block-`(0,k)` integral,
  `r = n + (0 + k + 1)`): for `u ∈ U_(n+2,r+1)` and `g ∈ GL_(n+1)(F)` there is
  `u' ∈ U_(r+1)` with `Σ u' = Σ u` and
  `diag(g, I) · u = u' · diag(g, I)`. The proof takes
  `u' = diag(g, I) u diag(g, I)⁻¹`. If `u = [1, Q; 0, S]`, then
  `u' = [1, g Q; 0, S]`. It is upper unitriangular by
  `upperUnitriangular_of_blockForm`, and since the first column of `g Q` is
  `g` times the zero first column of `Q`, `superdiag_sum_of_blockForm` gives
  `Σ u' = Σ S = Σ u`.
- `dualUnipotent_identity` (JPSS (2.11.4) for the complementary integral,
  block `(k, 0)`, `r = n + (k + 0 + 1)`): for `u ∈ U_(n+2,r+1)` there are
  `n₀ ∈ U_(r+1)`, `A : Matrix (Fin k) (Fin k) F` and
  `c : Matrix (Fin k) (Fin (n + 1)) F` such that `det A = 1`,
  `Σ n₀ = -Σ u`, and for all `g` and `x`,

  `M_(k,0)(g, x) · w_B · u⁻ᵀ = n₀ · M_(k,0)(g, A x + c) · w_B`.

  Construction. Write `u⁻¹ = [1, Q'; 0, D']` by `covarianceUnipotent_blocks`,
  so `u⁻ᵀ = [1, 0; Q'ᵀ, D'ᵀ]`. Regard the lower-right block `D` of `u` as an
  element `Dunip` of `U_(k+1)`, let
  `N = reflectedUnipotent Dunip = w D⁻ᵀ w` (published, `DualTransform`) and
  `V = N⁻¹`, both in `U_(k+1)`. Set `n₀ = diag(1, N)` (reindexed `blockSum`),
  `A` = the leading `k × k` block of `V`, and `c` = the first `k` rows of
  `V · w · Q'ᵀ`. In block form, with `X = stackRows (k+1) x`, the left side is
  `[g, 0; X + w Q'ᵀ, w D'ᵀ]` and the right side is `[g, 0; N X'', N w]`, where
  `X'' = stackRows (k+1) (A x + c)`. The lower-right blocks agree because
  `N w = w D'ᵀ` (from `w w = 1`). For the lower-left blocks, the proof shows
  `X'' = V (X + w Q'ᵀ)` row by row. In the last row, `V` has last row `e_last`
  (it is upper unitriangular), `X` has a zero last row, and the last row of
  `w Q'ᵀ` is the first column of `Q'`, which vanishes. The other rows are the
  definitions of `A` and `c`. Then `N X'' = N V (X + w Q'ᵀ) = X + w Q'ᵀ`.
  `A` is upper unitriangular, so `det A = 1` by `det_of_isUpperTriangular`.
  Finally `Σ n₀ = Σ N` by `superdiag_sum_of_blockForm`, `Σ u = Σ D` likewise,
  and the published `reflectedUnipotent_sum` gives `Σ N = -Σ D`.

## Provenance

JPSS = H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, Amer. J. Math. **105** (1983), §2.11, printed pp.398–399
(one-based PDF pages 33–34 of the registered scan `jpss-1983-rankin-selberg`).
Printed ranks `r, t` are Lean `r + 1, n + 1`. JPSS (2.11.3) defines
`U_{t,r}` as the matrices `(1_t u₂; 0 u₁)` with `u₁` upper unipotent. Its
Lean counterpart for `U_{t+1,r}` is the published
`IsUnequalRankCovarianceUnipotent n`. (2.11.4) asserts the unipotent laws "as
before", without proof. The two identities `originalUnipotent_identity` and
`dualUnipotent_identity` are this proof's own matrix computations behind
(2.11.4) for the two integrals. They do not appear in JPSS, and the choice of
`n₀`, `A` and `c` is internal to this proof. The block coordinates and every
other declaration here are internal bookkeeping. The current registration,
the central library, and the project and Library note locations were checked
for errata. No registered erratum to JPSS 1983 was found. The registered
Jacquet 2012 correction concerns the 1981 conductor paper only.
