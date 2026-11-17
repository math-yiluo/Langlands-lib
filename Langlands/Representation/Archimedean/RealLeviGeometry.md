# Geometry of the opposite unipotent radical of a standard parabolic subgroup of `GL_N(ℝ)`

Lean module: `Langlands.Representation.Archimedean.RealLeviGeometry`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It is
internal infrastructure for the limit argument along the parabolic subgroup `Q` whose blocks are
the tie classes of the Langlands order. All results are elementary linear algebra. No literature
statement is claimed, and nothing here is cited from a source.

The module states and proves one proposition, `RealLeviGeometryStatement` (proof
`realLeviGeometry`). The proposition collects the main lemmas of the module, listed below.

## Notation

The block data come from the module `RealLeviChartIntegralStatement`: `c` blocks of sizes
`sz : Fin c → ℕ`, matrix size `N = ∑ i, sz i`, `cls sz p` the block of the position `p`,
`Coord sz` the pairs `(p, q)` with `cls q < cls p`, `lower sz X = n̄(X)` the lower block
unitriangular matrix with entries `X` below the diagonal blocks, and `lowerGL sz X` the same matrix
in `GL_N(ℝ) = Langlands.GeneralLinear N ℝ`. `blockDiagHom` and `blockDiagGL` (block diagonal
matrices) come from `RealLeviParabolicIntegrationStatement`. `G_l = GramFormula.gram l` (module
`PrincipalSeriesGramFormula`) is the Gram determinant `det(A Aᵀ)` of the rows `l, …, N−1` of a
matrix, computed as the determinant of `paddedGram l`, the Gram matrix of these rows padded by the
identity. `GramFormula.padded l W` is `W` on the rows and columns `≥ l`, padded by the identity.
Unless stated otherwise, the declarations are in the namespace `Langlands.Archimedean.RealLeviChart`.

## The statement

`RealLeviGeometryStatement` (namespace `Langlands.Archimedean`) says: for all `c` and `sz`,

1. `1 ≤ G_l(n̄(X))` for all `X : Coord sz → ℝ` and all `l : ℕ`;
2. `G_l(n̄(X_s)) ≤ G_l(n̄(X))` for all `s ≥ 1`, `X` and `l`, where `X_s = scaleCoord sz s X`;
3. `n̄(X) d_s = d_s n̄(X_s)` in `GL_N(ℝ)` for all `s > 0` and `X`, where `d_s = scaleGL sz hs`;
4. `g n̄(X) = n̄(Ad(g) X) g` for every `g ∈ blockOrth sz` and every `X`, where
   `Ad(g) X = adCoord g X`;
5. `Ad(g)` preserves the Lebesgue measure `volume` on `Coord sz → ℝ`, for every `g ∈ blockOrth sz`;
6. `Ad(g) (X_s) = (Ad(g) X)_s` for every `g ∈ blockOrth sz`, `s > 0` and `X`.

Here:

* `scaleVec sz s p = s^{cls p}` (the block index as a natural number), and
  `d_s = scaleGL sz hs` is the diagonal matrix `diag(scaleVec sz s)` in `GL_N(ℝ)`, for `s > 0`
  (`hs : 0 < s`). It is central in the Levi factor of `Q`.
* `scaleCoord sz s X` is `X_s`, with `(X_s)_{pq} = s^{cls q} / s^{cls p} · X_{pq}`.
* `BlockZero sz k` means that `k p q = 0` whenever `cls p ≠ cls q`. `blockOrth sz` is the subgroup
  of `GL_N(ℝ)` of the elements `g` with `g gᵀ = 1` and `BlockZero sz g`, i.e. the orthogonal
  matrices in the Levi factor of `Q`, which is `∏_i O(sz_i)` embedded block diagonally.
* `adCoord k X` is the family of entries `(k n̄(X) kᵀ)_{pq}` for `(p, q) ∈ Coord sz`.

Edge cases. If `l ≥ N`, then `G_l = 1` for every matrix, so 1 and 2 hold trivially. If `c ≤ 1`,
then `Coord sz` is empty and every statement about `X` is about the single point of
`Coord sz → ℝ`.

## Further results

* `blockRotation_mem_blockOrth`: the Library rotation `r_p(θ) = blockRotation N p θ` in the
  coordinates `p, p+1` belongs to `blockOrth sz` when `p` and `p + 1` lie in the same block.
* `blockDiagGL_mem_blockOrth`, `blockDiagGL_mem_unitaryCompact`: `diag(κ_0, …, κ_{c−1})` with
  `κ_i ∈ O(sz_i)` belongs to `blockOrth sz` and to `O(N) = unitaryCompact ℝ N`.
* `mem_blockOrth_of_mem_unitaryCompact`, `mem_unitaryCompact_of_mem_blockOrth`: `blockOrth sz` is
  the set of elements of `O(N)` satisfying `BlockZero sz`.
* `mul_scaleGL`: block orthogonal elements commute with `d_s`.
* `lower_injective`, `cls_mono`, `lower_scaleCoord`
  (`n̄(X_s) = d_s⁻¹ n̄(X) d_s` as matrices), `lower_adCoord` (`n̄(Ad(k) X) = k n̄(X) kᵀ`).
* Determinant inequalities (section `Det`): `det A ≤ det(A + Cᵀ C)` for positive definite `A`
  (`det_le_det_add_transpose_mul_self`), and
  `det(1 + (a Y b)(a Y b)ᵀ) ≤ det(1 + Y Yᵀ)` for diagonal matrices `a`, `b` with entries of absolute
  value `≤ 1` (`det_one_add_contraction_le`).
* Gram determinants (section `Gram`): `gram_eq_of_lower`, `one_le_gram_of_lower` and
  `gram_conj_le` for arbitrary lower unitriangular matrices (see the proof below).

## Proof

**Determinant inequalities.** For positive definite `A`, Mathlib's `Matrix.det_add_mul` gives
`det(A + Cᵀ C) = det A · det(1 + C A⁻¹ Cᵀ)`. The matrix `C A⁻¹ Cᵀ` is positive semidefinite, so
`det(1 + C A⁻¹ Cᵀ) ≥ 1` by `RealBlockLimit.one_le_det` (from my module `RealBlockLimit`, an
accepted candidate that is present in the workspace). For the contraction inequality, write
`Y' = a Y b`. By Sylvester's identity (`Matrix.det_one_add_mul_comm`),
`det(1 + Y' Y'ᵀ) = det(1 + Y'ᵀ Y')`. Then `1 + (Y b)ᵀ (Y b) = 1 + Y'ᵀ Y' + C₁ᵀ C₁` with
`C₁ = diag(√(1 − a_i²)) Y b`, so the first inequality gives
`det(1 + Y'ᵀ Y') ≤ det(1 + (Y b)ᵀ (Y b))`. By Sylvester again and the same argument with
`C₂ = diag(√(1 − b_i²)) Yᵀ`, `det(1 + (Y b)(Y b)ᵀ) ≤ det(1 + Y Yᵀ)`.

**Gram determinants of lower unitriangular matrices.** Fix `l` and a lower unitriangular `L`
(lower triangular with diagonal entries `1`).

* If `W` has no entries in the rows `≥ l` and columns `< l`, then
  `paddedGram l (W Z) = padded l W · paddedGram l Z · (padded l W)ᵀ`
  (`paddedGram_mul_of_blockUpper`). If moreover `W` is lower unitriangular, then
  `det(padded l W) = 1`, so `G_l(W Z) = G_l(Z)` (`gram_mul_of_blockUpper`).
* If `Z` equals the identity on the rows and columns `≥ l`, then
  `paddedGram l Z = 1 + Y Yᵀ`, where `Y = lowerLeft l Z` is the block of `Z` on the rows `≥ l` and
  columns `< l`, padded by zeros (`paddedGram_of_block_one`).
* `L = W Z` with `W = splitDiag l L` the block diagonal part of `L` for the splitting of the
  indices at `l` (lower unitriangular), and `Z = splitFactor l L = W⁻¹ L`. The factor `Z` is the
  identity on the rows and columns `≥ l` (`splitFactor_block_one`: with the projection `P` onto
  the coordinates `≥ l`, `P L P = W P` and `W` commutes with `P`, so `P Z P = P`).
* Hence `G_l(L) = det(1 + Y Yᵀ)` with `Y = lowerLeft l (splitFactor l L)` (`gram_eq_of_lower`),
  and `1 ≤ G_l(L)` by the first determinant inequality with `A = 1` (`one_le_gram_of_lower`).
* **Monotonicity** (`gram_conj_le`). Let `d` be a positive vector and `μ > 0` with `d_q ≤ μ` for
  `q < l` and `d_p ≥ μ` for `p ≥ l`. Then `D⁻¹ L D = (D⁻¹ W D)(D⁻¹ Z D)`, with `D = diag(d)`. The
  first factor is again lower unitriangular without entries in the rows `≥ l` and columns `< l`,
  and the second is the identity on the rows and columns `≥ l`. So
  `G_l(D⁻¹ L D) = det(1 + Y' Y'ᵀ)` with `Y' = a Y b`, where `a_p = μ / d_p` for `p ≥ l` and `0`
  otherwise, and `b_q = d_q / μ` for `q < l` and `0` otherwise. All entries of `a` and `b` lie in
  `[0, 1]`, and the contraction inequality gives `G_l(D⁻¹ L D) ≤ G_l(L)`.

**Scaling.** `n̄(X) diag(s^{cls p}) = diag(s^{cls p}) n̄(X_s)` is checked entrywise
(`lower_mul_diagonal`, `lowerGL_mul_scaleGL`), and gives `n̄(X_s) = d_s⁻¹ n̄(X) d_s`. For `s ≥ 1`
and `l < N`, the weights `d_p = s^{cls p}` are monotone in `p` (`cls_mono`), so `μ = s^{cls l}`
satisfies the hypotheses of `gram_conj_le`; this is statement 2 (`gram_lower_scaleCoord_le`).
Statement 1 is `one_le_gram_lower`.

**Block orthogonal conjugation.** `blockOrth sz` is a subgroup: products and inverses
(`g⁻¹ = gᵀ`) of orthogonal matrices without entries between different blocks have the same
property. For `k` with `k kᵀ = 1` and `BlockZero sz k`, the entries `(p, q)` of `k n̄(X) kᵀ` with
`cls q ≥ cls p` agree with those of `k kᵀ = 1`, because in the sum
`∑_{r,t} k_{pr} n̄(X)_{rt} k_{qt}` only terms with `cls r = cls p` and `cls t = cls q` survive, and
for these `n̄(X)_{rt} = 1_{rt}` (`lower_conj_apply_of_not_lt`). So `k n̄(X) kᵀ = n̄(Ad(k) X)`
(`lower_adCoord`), and `g n̄(X) = n̄(Ad(g) X) g` (`mul_lowerGL`, statement 4). A block diagonal
matrix `D` with entries constant on each block commutes with every `k` satisfying `BlockZero`
(`commute_diagonal_of_blockZero`); applied to `d_s` and `d_s⁻¹` this gives `mul_scaleGL` and,
with `lower_scaleCoord` and `lower_injective`, statement 6 (`adCoord_scaleCoord`).

**Measure.** Write `n̄(X) = 1 + S(X)` with `S(X) = strict X` the strictly lower block part. Then
`Ad(k) X` consists of the entries of `k S(X) kᵀ` at `Coord sz` (`adCoord_eq`). This is linear in
`X` (`adLin`). The entries of `k S(X) kᵀ` outside `Coord sz` vanish (by the previous paragraph), so
`∑_{pq ∈ Coord} (Ad(k) X)_{pq}² = ∑_{p,q} (k S kᵀ)_{pq}² = tr(k S Sᵀ kᵀ) = tr(S Sᵀ) = ∑_{pq} X_{pq}²`
(`sum_coord_sq`, `sum_sq_conj`, `sum_sq_adCoord`). So `Ad(k)` is a linear isometry of the
Euclidean space `EuclideanSpace ℝ (Coord sz)`; it is surjective because it is injective in finite
dimension (`LinearIsometry.toLinearIsometryEquiv`), and linear isometry equivalences preserve
Lebesgue measure (`LinearIsometryEquiv.measurePreserving`). Transporting along the
measure-preserving identifications `PiLp.volume_preserving_toLp`/`ofLp` with `Coord sz → ℝ` gives
statement 5 (`measurePreserving_adCoord`).

## Use

In the limit argument along `Q`, `d_s = diag(s^{cls p})` contracts `N̄_Q` (`n̄(X) d_s = d_s n̄(X_s)`)
and the Gram bounds dominate the integrands uniformly in `s ≥ 1`. The block orthogonal elements
are the elements of `K_M = ∏_i O(sz_i)` and the block rotations used to average over the tori of
the induction blocks; statement 4 moves them past `n̄(X)`, and statements 5 and 6 allow the
substitution `X ↦ Ad(g) X` in the integrals over `N̄_Q`.
