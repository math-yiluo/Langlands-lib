# Block embeddings and slices for induction in stages

Module: `Langlands.Representation.Archimedean.RealInductionStagesSlice`.

## Purpose and provenance

This module is internal infrastructure for the proof of
`Langlands.Archimedean.RealAdjacentFiltrationInStagesStatement` (induction in stages of adjacent
filtrations, Task 7068). Let `a + r ≤ n`. The module embeds `GL_r(ℝ)` into `GL_n(ℝ)` as the
middle diagonal block

`ι(h) = diag(1_a, h, 1_(n-a-r))`.

For a function `F` on `GL_n(ℝ)` and `κ ∈ GL_n(ℝ)`, the slice of `F` at `κ` is the function

`σ_κ F (h) = ν(h) F(ι(h) κ)`, where `ν(h) = |det h|^(-c)` and `c = (n - r)/2 - a`.

Let `F` lie in the real standard module of `pre ++ ds ++ post`, where `pre` has rank `a`, `ds`
has rank `r` and the three ranks add up to `n`. Then every slice of `F` lies in the real
standard module of `ds`. When `κ ∈ O(n)` and `F` is `O(n)`-finite, the slice is `O(r)`-finite.
This is the function-level form of the map `F ↦ F(·)(1)` in induction in stages; see
Knapp–Vogan, *Cohomological Induction and Unitary Representations*, (11.196). The module proves
only the statements listed below and makes no other literature claim.

The exponent `c` is the shift that makes the modular characters agree. Position `a + j` of the
`GL_n` principal-series character carries `|t|^((n-1)/2 - (a+j))`. Position `j` of the `GL_r`
character carries `|t|^((r-1)/2 - j)`. These differ by `|t|^c`, and `ν` removes this
difference (`sliceFactor_mul_principalSeriesCharacter`).

All declarations are in the namespace `Langlands.Archimedean.InductionStages`. Throughout,
`n a r : ℕ` and `h : a + r ≤ n`. `GL_m(ℝ)` is `Langlands.GeneralLinear m ℝ`, and
`O(m) = unitaryCompact ℝ m`.

## Declarations

### The coordinate embedding

- `IsMid a r i`: the coordinate `i : Fin n` is a middle coordinate, `a ≤ i < a + r`
  (decidable).
- `idx h j : Fin n`: the middle coordinate `a + j` for `j : Fin r` (`idx_val`). Lemmas:
  `isMid_idx`, `idx_injective`, `exists_idx_of_isMid` (each middle coordinate is some
  `idx h j`), and `not_isMid_iff_not_mem_range`.
- `embMat n a r`: the `n × r` matrix `P` with `P i j = 1` if `i = a + j` and `0` otherwise.
  Lemmas: `embMat_mul_apply_idx` (`(P M) (a+k) l = M k l`), `embMat_mul_apply_of_not_isMid`
  (rows of `P M` outside the middle are zero), the transposed versions
  `mul_embMat_transpose_apply_idx` and `mul_embMat_transpose_apply_of_not_isMid`, and
  `embMat_transpose_mul_embMat` (`Pᵀ P = 1`).
- `blockMat n a r y = 1 + P (y - 1) Pᵀ` for an `r × r` matrix `y`, the matrix
  `diag(1_a, y, 1)`. Lemmas: `blockMat_apply_idx` (middle entries are those of `y`),
  `blockMat_apply_of_not_isMid_left` and `_right` (a row or column outside the middle agrees
  with the identity matrix), `blockMat_one`, `blockMat_mul` (multiplicative, from `Pᵀ P = 1`),
  `blockMat_transpose`.
- `blockEmb h : GL_r(ℝ) →* GL_n(ℝ)`: the group homomorphism `ι` with matrix `blockMat`
  (`blockEmb_val`). `blockEmb_mem_unitaryCompact`: `ι` maps `O(r)` into `O(n)`, because
  `blockMat` respects transposes and products.

### Positions in concatenated lists

- `realRank_append'`: `realRank (xs ++ ys) = realRank xs + realRank ys`.
- `rank_character`, `rank_induced`: character blocks have rank 1 and induced blocks rank 2.
- `realPositionCharacter_append_left pre M k`: position `realRank pre + k` of `pre ++ M` has
  the character of position `k` of `M`. `realPositionCharacter_append_right ds post k`: if
  `k < realRank ds`, position `k` of `ds ++ post` has the character of position `k` of `ds`.
  Both are proved by induction on the list.
- The same two statements for exponents (`realPositionExponent_append_left`, `_right`) and
  for induction blocks (`realInducedBlockAt_append_left`, `_right`).
- `realInducedBlockAt_append_cases`: an induction block of `pre ++ M` at position `p` lies
  either inside `pre` (`p + 1 < realRank pre`, same block in `pre`) or inside `M`
  (`realRank pre ≤ p`, same block at position `p - realRank pre` of `M`). Induction blocks
  never straddle the boundary.

### The factor `ν`

- `sliceExponent n a r = (n - r)/2 - a` (a complex number), and
  `sliceFactor n a r g = |det g|^(-sliceExponent n a r)` (a complex power of a nonnegative real
  number).
- `sliceFactor_mul`: `ν` is multiplicative (`Complex.mul_cpow_ofReal_nonneg`).
- `sliceFactor_of_abs_det_eq_one`: `ν(g) = 1` if `|det g| = 1`. Consequences:
  `sliceFactor_one`, `sliceFactor_of_mem_unitaryCompact` (orthogonal matrices have determinant
  `±1`), `sliceFactor_of_mem_upperUnipotent`.
- `cpow_prod_ofReal`: a complex power of a finite product of nonnegative reals is the product
  of the powers, by induction on the finite set.
- `sliceFactor_diagonalUnits`: `ν(diag t) = ∏_j |t_j|^(-c)`.
- `contDiffAt_sliceFactor`: `y ↦ |det y|^(-c)` is smooth at every invertible matrix `y`, by
  smoothness of `det`, of `|·|` away from `0`, and of complex powers of positive reals
  (`PrincipalSeriesExtension.contDiffAt_ofReal_cpow`).

### The torus, the unipotent group and the rotations

- `extUnits h t : Fin n → ℝˣ`: the family `t : Fin r → ℝˣ` placed on the middle coordinates,
  with `1` elsewhere (`extUnits_idx`, `extUnits_of_not_isMid`).
- `blockEmb_diagonalUnits`: `ι(diag t) = diag(extUnits h t)`.
- `blockEmb_mem_upperUnipotent`: `ι` maps the upper unipotent group of `GL_r(ℝ)` into that of
  `GL_n(ℝ)`.
- `sliceFactor_mul_principalSeriesCharacter`: let `χ` and `ψ` be families of characters of
  `ℝˣ` with `χ (a + j) = ψ j` for `j < r` and `χ i 1 = 1` for all `i`. Then
  `ν(diag t) · δχ_n(extUnits h t) = δχ_r(t)`, where `δχ_m` is the Library's
  `principalSeriesCharacter ℝ m` (character times the modular factor). Proof: positions outside
  the middle contribute `1` (`Fintype.prod_of_injective` along `idx h`). At position `a + j`
  the two modular exponents differ by `c`, which `ν` cancels.
- `blockEmb_blockRotation`: `ι(r_p(θ)) = r_(a+p)(θ)` for `p + 1 < r`, where `r_p(θ)` is the
  Library's `blockRotation` (rotation by `θ` in coordinates `p, p + 1`). Proof: compare
  entries with `RealBlockRotation.blockRotation_apply`.

### Slices

- `slice h κ : (GL_n(ℝ) → ℂ) →ₗ[ℂ] (GL_r(ℝ) → ℂ)`: the linear map
  `F ↦ (g ↦ ν(g) F(ι(g) κ))` (`slice_apply`).
- `slice_apply_one`: `σ_κ F (1) = F(κ)`.
- `slice_translate`: `σ_κ (x ↦ F(x κ')) = σ_(κ κ') F`.
- `slice_mul_apply`: `σ_κ F (g g₀) = ν(g₀) · σ_(ι(g₀) κ) F (g)`.
- `contDiff_blockMat_mul`: `y ↦ blockMat y · κ` is smooth (an affine map of matrices).
- `contMDiff_slice`: the slice of a smooth function on `GL_n(ℝ)` is smooth on `GL_r(ℝ)`.
  Proof: `contMDiff_of_contDiffOn` with the function
  `y ↦ |det y|^(-c) · F̃(blockMat y · κ)` on matrices, where `F̃` is the Library's
  `unitsExtension F`, smooth on the invertible matrices (`contDiffOn_unitsExtension`).
- `slice_mem_principalSeries h hχ h1 κ hF`: under the hypotheses of
  `sliceFactor_mul_principalSeriesCharacter`, if `F ∈ principalSeries ℝ n χ` then
  `σ_κ F ∈ principalSeries ℝ r ψ`. Proof: smoothness by `contMDiff_slice`. For the
  equivariance, `ι(diag t · u · g) κ = diag(extUnits h t) · ι(u) · (ι(g) κ)` with `ι(u)` upper
  unipotent. Then apply the equivariance of `F`, `ν(u) = 1` and
  `sliceFactor_mul_principalSeriesCharacter`.
- `blockFourierCoefficient_slice`: for `p + 1 < r`, the `k`-th Fourier coefficient of `σ_κ F`
  along `r_p` at `g` equals `ν(g)` times the `k`-th Fourier coefficient of `F` along `r_(a+p)`
  at `ι(g) κ` (Library `blockFourierCoefficient`). Proof: `ν(r_p(θ)) = 1` and
  `blockEmb_blockRotation`.
- `slice_mem_realStandardModule h ha hr κ hF`: if `realRank pre = a`, `realRank ds = r` and
  `F ∈ realStandardModule n (pre ++ ds ++ post)`, then `σ_κ F ∈ realStandardModule r ds`, for
  every `κ ∈ GL_n(ℝ)`. The list `pre ++ ds ++ post` is parsed as `(pre ++ ds) ++ post`. Proof:
  the principal-series part is `slice_mem_principalSeries`. Its hypotheses come from the list
  lemmas and `RealStrictCharacterLanglandsQuotient.realPositionCharacter_one`. For the Fourier
  vanishing, an induction block of `ds` at position `p` is the induction block of
  `pre ++ ds ++ post` at position `a + p`. Apply `blockFourierCoefficient_slice`.
- `slice_mem_kFiniteVectors`: for `κ ∈ O(n)`, if the right `O(n)`-translates of `F` span a
  finite-dimensional space, so do the right `O(r)`-translates of `σ_κ F`. Proof: the
  `O(r)`-translate of `σ_κ F` by `k` is `σ_κ` of the translate of `F` by
  `κ⁻¹ ι(k) κ ∈ O(n)`. So the span of the `O(r)`-translates lies in the image under `σ_κ` of a
  finite-dimensional space.
- `slice_mem_kFin`: combining the two, for `κ ∈ O(n)` the slice maps `KFin n (pre ++ ds ++ post)`
  into `KFin r ds` (the `O(m)`-finite functions in the real standard module, from
  `RealInductionStagesAverage`).
- `blockEmbK h : O(r) →* O(n)`: `ι` restricted to the orthogonal groups (`coe_blockEmbK`).
- `sliceK h ha hr κ : KFin n (pre ++ ds ++ post) →ₗ[ℂ] KFin r ds`: the slice at `κ ∈ O(n)` as
  a linear map between the `O(n)`- and `O(r)`-finite functions (`sliceK_apply_coe`).
  `sliceK_apply_one`: `σ_κ F (1) = F(κ)`.
- `sliceK_kRep`: `σ_κ (R(κ') F) = σ_(κ κ') F` for `κ' ∈ O(n)`, where `R` is the right
  translation `kRep` of `RealInductionStagesAverage`.
- `kRep_sliceK`: `R(k) (σ_κ F) = σ_(ι(k) κ) F` for `k ∈ O(r)`, by `slice_mul_apply` and
  `ν(k) = 1`.
