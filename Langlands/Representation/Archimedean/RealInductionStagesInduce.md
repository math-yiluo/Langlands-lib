# Induction in stages of `O(r)`-equivariant maps

Module: `Langlands.Representation.Archimedean.RealInductionStagesInduce`.

## Purpose and provenance

This module is internal infrastructure for the proof of
`Langlands.Archimedean.RealAdjacentFiltrationInStagesStatement` (induction in stages of adjacent
filtrations). Let

`L' = pre ++ ds' ++ post` and `L = pre ++ ds ++ post`

be lists of real blocks, with `realRank pre = a`, `realRank ds = realRank ds' = r`,
`a + r ≤ n` and `realRank L = n`. Let `T : KFin r ds' →ₗ[ℂ] KFin r ds` be a linear map between
the `O(r)`-finite functions of the two standard modules on `GL_r(ℝ)`. Suppose that `T`
commutes exactly with right translation by `O(r)`:

`hT : ∀ k f, T (kRep r ds' k f) = kRep r ds k (T f)`.

The module constructs the induced map

`ind h ha hr hr' hn T hT : KFin n L' →ₗ[ℂ] KFin n L`,

with `(ind T F)(κ) = (T σ_κ F)(1)` for `κ ∈ O(n)`. Here `σ_κ` is the slice `sliceK` of
`RealInductionStagesSlice`. The function on `O(n)` is extended to `GL_n(ℝ)` by the Library's
`PrincipalSeriesExtension.extension`. The module proves that `ind T F` lies in the real
standard module of `L` and is `O(n)`-finite. It also proves that `ind T` commutes exactly with
`O(n)` (`ind_kRep`) and that `σ_κ (ind T F) = T (σ_κ F)` for `κ ∈ O(n)` (`sliceK_ind`).

This is the function-level form of applying induction in stages to `T`: compare the
description of induced representations in stages in Knapp–Vogan, *Cohomological Induction and
Unitary Representations*, (11.196). The module proves only the statements listed below and
makes no other literature claim.

All declarations are in the namespace `Langlands.Archimedean.InductionStages`. `GL_m(ℝ)` is
`Langlands.GeneralLinear m ℝ` and `O(m) = unitaryCompact ℝ m`. The block embedding
`ι = blockEmb h`, the matrices `blockMat`, `embMat`, the factor `ν = sliceFactor n a r` and the
predicate `IsMid a r` are those of `RealInductionStagesSlice`.

## Declarations

### Orthogonal matrices

- `ofUnitary n : Matrix.unitaryGroup (Fin n) ℝ →* unitaryCompact ℝ n`: the orthogonal matrices
  as the subgroup `O(n)` of `GL_n(ℝ)`. It is inverse to `toUnitary`
  (`toUnitary_ofUnitary`, `ofUnitary_toUnitary`). `coe_ofUnitary` gives the underlying
  element of `GL_n(ℝ)`.
- `continuous_toUnits'`: the map from orthogonal matrices to `GL_n(ℝ)` is continuous.
- `toUnits_signDiagonal d`: the sign diagonal matrix of `d : Fin n → ℝˣ` is the diagonal unit
  with entries `signUnit (d i)`.

### Positions outside and inside the middle

- `append_outside f hl hr hds hi`: let `f : List RealBlock → ℕ → β` satisfy the shift laws
  `f (pre ++ M) (realRank pre + k) = f M k` and `f (ds ++ post) k = f ds k` for
  `k < realRank ds`. If `realRank ds = realRank ds'`, then `f (pre ++ ds ++ post) i` and
  `f (pre ++ ds' ++ post) i` agree at every position `i` outside the middle range
  `[realRank pre, realRank pre + realRank ds)`.
- `append_mid f hl hr hj`: `f (pre ++ ds ++ post) (realRank pre + j) = f ds j` for
  `j < realRank ds`.

These are applied below to `realPositionCharacter`, `realPositionExponent` and
`realInducedBlockAt`, using the shift laws of `RealInductionStagesSlice`.

### Diagonal matrices and the middle block

- `outUnits a r t`: `t` off the middle coordinates and `1` on them. `midUnits h t`: the middle
  coordinates of `t`, as a function on `Fin r`.
- `outUnits_mul_extUnits`: `t = outUnits t * extUnits (midUnits t)`.
- `diagonalUnits_outUnits_mul_blockEmb`: `diag(outUnits t)` commutes with every `ι(g)`.
  Proof: entrywise; the diagonal entries of `outUnits t` are `1` on the middle coordinates,
  and `ι(g)` agrees with the identity outside the middle block.
- `diagonalUnits_eq_mul`: `diag(t) = diag(outUnits t) ι(diag(midUnits t))`.
- `principalSeriesCharacter_outUnits_mul`: the principal-series character of `t` is the product
  of its values at `outUnits t` and at `extUnits (midUnits t)`, for characters with
  `χ i 1 = 1`. `principalSeriesCharacter_outUnits_congr`: its value at `outUnits t` depends
  only on the characters at the coordinates outside the middle.
- `sliceFactor_diagonalUnits_signUnit`: `ν` is `1` on sign diagonal matrices.
- `slice_diagonalUnits_mul hF t κ g`: for `F` in the principal series of `χ`,
  `σ_{diag(t) κ} F (g) · ν(diag(t_mid)) = χ(t_out) · σ_κ F (g diag(t_mid))`. Proof: rewrite
  `ι(g) diag(t) κ = diag(t_out) · 1 · ι(g diag(t_mid)) κ` and use the left equivariance of `F`
  and the multiplicativity of `ν`.

### The function on `O(n)`

From here on, `h : a + r ≤ n`, `ha : realRank pre = a`, `hr : realRank ds = r` and
`hr' : realRank ds' = r`.

- `realPositionCharacter_outside`, `realPositionExponent_outside`,
  `realInducedBlockAt_outside`: at positions `i < a` or `i ≥ a + r` the position characters,
  position exponents and induction blocks of `L` and `L'` agree (`append_outside`).
  `realPositionCharacter_mid`: the character of `L` at `a + j` is the character of `ds` at `j`.
- `indFun h ha hr' T`: the linear map `F ↦ (κ ↦ (T σ_κ F)(1))` from `KFin n L'` to functions on
  the orthogonal matrices (`indFun_apply`).
- `indFun_mul`: `indFun T F (κ k) = indFun T (R(k) F) (κ)`, from `sliceK_kRep`.
- `continuous_indFun`: `indFun T F` is continuous. Proof: it equals
  `κ ↦ ((T ∘ σ_1)(R(κ) F))(1)`. The vectors `R(κ) F` stay in the finite-dimensional orbit span
  of `F` and depend continuously on `κ` pointwise, so `continuous_map_of_mem`
  (`RealInductionStagesFamily`) applies.
- `finiteDimensional_indFun`: the span of the right translates of `indFun T F` is
  finite-dimensional. It lies in the image under `indFun T` of the orbit span of `F`, by
  `indFun_mul`.
- `indFun_signDiagonal_mul hT F d κ`: for every `d : Fin n → ℝˣ`,
  `indFun T F (sgn(d) κ) = χ_L(sgn d) · indFun T F (κ)`, where `χ_L` is the principal-series
  character of `realPositionCharacter L`. Proof. By `slice_diagonalUnits_mul`, the slice at
  `sgn(d) κ` is `χ_{L'}(sgn(d)_out) · R(k_mid) σ_κ F`, where `k_mid ∈ O(r)` is the sign
  diagonal matrix of the middle coordinates. By `hT`, applying `T` and evaluating at `1` gives
  `(T σ_κ F)(diag(sgn(d)_mid))`. This equals `χ_ds(sgn(d)_mid) (T σ_κ F)(1)`, by the left
  equivariance of `T σ_κ F`. Finally
  `χ_{L'}(sgn(d)_out) χ_ds(sgn(d)_mid) = χ_L(sgn d)`, because the characters of `L` and `L'`
  agree outside the middle, the characters of `L` in the middle are those of `ds`
  (`sliceFactor_mul_principalSeriesCharacter`), and `ν(sgn) = 1`.

### Rotations outside the middle block

- `mul_embMat_eq`, `embMat_transpose_mul_eq`, `mul_blockMat_comm`: a matrix `M` that agrees
  with the identity on all middle rows and all middle columns satisfies `M P = P` and
  `Pᵀ M = Pᵀ`, so it commutes with every `blockMat y = 1 + P (y - 1) Pᵀ`.
- `blockRotation_mul_blockEmb h hp hout θ g`: if `p + 1 < n` and the rotation plane
  `{p, p + 1}` lies outside the middle (`p + 1 < a` or `a + r ≤ p`), then the rotation
  `blockRotation n p θ` commutes with every `ι(g)`. Proof: `mul_blockMat_comm`, with the
  entries of the rotation from `RealBlockRotation.blockRotation_apply`.
- `rotK n p θ`: the rotation as an element of `O(n)` (`coe_rotK`).

### The extension to `GL_n(ℝ)`

Let also `hn : realRank L = n`.

- `indExt h ha hr' T`: the linear map
  `F ↦ extension (shiftedExponent n (realPositionExponent L)) (indFun T F)`, using the Library's
  `PrincipalSeriesExtension.extensionLinear` (`indExt_apply`).
- `indExt_unitaryCompact`: `indExt T F κ = (T σ_κ F)(1)` for `κ ∈ O(n)`, by
  `PrincipalSeriesExtension.extension_unitary`.
- `indExt_mem hT F`: `indExt T F` is an `O(n)`-finite function in the principal series of
  `realPositionCharacter L`. This is `PrincipalSeriesExtension.extension_mem_kFiniteFunctions`,
  with `realPositionCharacter_eq_signUnit_mul`, `continuous_indFun`,
  `finiteDimensional_indFun` and `indFun_signDiagonal_mul`.
- `indExt_blockEmb hT F κ k`: `indExt T F (ι(k) κ) = (T σ_κ F)(k)` for `k ∈ O(r)`, by
  `kRep_sliceK` and `hT`.
- `slice_indExt hT F κ` (**slice identity**): `σ_κ (indExt T F) = T (σ_κ F)` as functions on
  `GL_r(ℝ)`, for `κ ∈ O(n)`. Proof: both sides lie in the principal series of
  `realPositionCharacter ds` (`slice_mem_principalSeries`). They agree on `O(r)` by
  `indExt_blockEmb` and `ν(k) = 1`, so they are equal by the Library's
  `eq_of_eqOn_unitaryCompact_of_mem_principalSeries`.
- `blockFourierCoefficient_indExt_outside F hp hout j hF κ`: if the rotation plane `{p, p + 1}`
  lies outside the middle and every block Fourier coefficient `(p, j)` of `F` vanishes on
  `GL_n(ℝ)`, then the coefficient `(p, j)` of `indExt T F` vanishes at every `κ ∈ O(n)`. Proof.
  The integrand `θ ↦ indExt T F (r_p(θ) κ) e^{-ijθ}` equals `θ ↦ (T w(θ))(1)`, where
  `w(θ) = e^{-ijθ} σ_{r_p(θ) κ} F` lies in the finite-dimensional image under `σ_1` of the orbit
  span of `F`. By `map_integral_of_mem` (with the measure `volume` restricted to `(0, 2π]`),
  the integral of `(T w(θ))(1)` is `(T v)(1)`, where `v` is the pointwise integral of `w`. Since
  `r_p(θ)` commutes with `ι(x)`, the integral of `w(θ)(x)` is
  `ν(x) · blockFourierCoefficient n p j F (ι(x) κ) = 0`. So `v = 0`.
- `blockFourierCoefficient_indExt hT F hd hj κ`: for every induction block `d` of `L` at a
  position `p`, every `j` with `|j| < |d.weight|` and every `κ ∈ O(n)`, the block Fourier
  coefficient `(p, j)` of `indExt T F` vanishes at `κ`. Proof: by
  `realInducedBlockAt_append_cases`, the block lies in `pre`, in `ds` or in `post`.
  - Outside the middle: the blocks of `L` and `L'` agree (`realInducedBlockAt_outside`).
    The coefficients of `F ∈ realStandardModule n L'` vanish everywhere, so
    `blockFourierCoefficient_indExt_outside` applies.
  - In the middle: `p = a + p'` with a block `d` of `ds` at `p'`. By
    `blockFourierCoefficient_slice`, the coefficient at `κ` is the coefficient `(p', j)` at `1`
    of `σ_κ (indExt T F) = T (σ_κ F)`. This vanishes because `T (σ_κ F)` lies in the real
    standard module of `ds`.
- `indExt_mem_kFin hT F`: `indExt T F ∈ KFin n L`. It combines `indExt_mem` with
  `blockFourierCoefficient_indExt` and `mem_realStandardModule_of_unitaryCompact`
  (`RealInductionStagesFourier`).

### The induced map

- `ind h ha hr hr' hn T hT : KFin n L' →ₗ[ℂ] KFin n L`: `indExt T` with its values in
  `KFin n L` (`ind_apply_coe`).
- `ind_apply_unitaryCompact`: `(ind T F)(κ) = (T σ_κ F)(1)` for `κ ∈ O(n)`.
- `ind_kRep κ' F`: `ind T (R(κ') F) = R(κ') (ind T F)` for `κ' ∈ O(n)`. Proof: both sides lie in
  the principal series of `realPositionCharacter L`. At `g ∈ O(n)` both equal
  `(T σ_{g κ'} F)(1)`, by `ind_apply_unitaryCompact` and `sliceK_kRep`. So they agree on all of
  `GL_n(ℝ)` by `eq_of_eqOn_unitaryCompact_of_mem_principalSeries`.
- `sliceK_ind κ F`: `σ_κ (ind T F) = T (σ_κ F)` in `KFin r ds`, for `κ ∈ O(n)`
  (`slice_indExt`).
