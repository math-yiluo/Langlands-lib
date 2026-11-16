# Induced maps and right derivatives

Module: `Langlands.Representation.Archimedean.RealInductionStagesDerivative`.

## Purpose and provenance

This module is internal infrastructure for the proof of
`Langlands.Archimedean.RealAdjacentFiltrationInStagesStatement` (induction in stages of adjacent
filtrations, Task 7068). It controls how the induced map `ind T` of
`RealInductionStagesInduce` interacts with right derivatives. Let
`T : KFin r ds' →ₗ[ℂ] KFin r ds` commute exactly with `O(r)`. Let `M` be a subspace of
`KFin r ds` such that `T R(Z) f - R(Z) T f ∈ M` for every real `r × r` matrix `Z` and every
`f`. Then the main theorem `sliceK_ind_lie_sub_mem` states that for every real `n × n` matrix
`X`, every `F ∈ KFin n (pre ++ ds' ++ post)` and every `κ ∈ O(n)`,

`σ_κ (ind T (R(X) F) - R(X) (ind T F)) ∈ M`.

The module makes no literature assertion. The proof splits `X` into three parts. It uses the
Library's formula for derivatives of exp-equivariant functions in upper triangular directions
(`RealBlockDerivative.fderiv_upperTriangular_of_isExpEquivariant`) and the derivative axiom of
the `(𝔤, K)`-module structure (`isRealGKModule_realStandardModule`).

All declarations are in the namespace `Langlands.Archimedean.InductionStages`. Notation is as
in `RealInductionStagesSlice` and `RealInductionStagesInduce`. `P = embMat n a r` is the
`n × r` matrix of the middle coordinates, so `blockMat y = 1 + P (y - 1) Pᵀ` and `PᵀP = 1`.
`R(X) = rightDerivative (matrixModel ℝ n) X` is the right derivative, and `σ_1 = slice h 1`.

## Declarations

### Matrix identities

- `embMat_transpose_mul_apply`, `mul_embMat_apply`: `(Pᵀ M) k l = M (a + k) l` and
  `(M P) l k = M l (a + k)`.
- `blockMat_mul_embMat`: `blockMat y · P = P y`. `blockMat_mul_mid`:
  `blockMat y · (P Z Pᵀ) = P (y Z) Pᵀ`.
- `mid_apply_idx`, `mid_apply_of_not_isMid_left`, `mid_apply_of_not_isMid_right`: the entries of
  `P Z Pᵀ` are `Z k l` at `(a + k, a + l)` and `0` in every row or column outside the middle.
- `midBlock n a r Y = Pᵀ Y P`, the middle block of `Y` (`midBlock_apply`).
- `lowerOut a r Y`: the entries `Y i j` with `j < i` and `(i, j)` not in the middle block, and
  `0` elsewhere. `skewOut a r Y = lowerOut Y - (lowerOut Y)ᵀ` is antisymmetric
  (`skewOut_transpose`).
- `upperOut n a r Y = Y - P (midBlock Y) Pᵀ - skewOut Y`, so that
  `Y = upperOut Y + P (midBlock Y) Pᵀ + skewOut Y` (`eq_upperOut_add`). `upperOut Y` is upper
  triangular (`upperOut_apply_of_lt`) and vanishes on the middle block (`upperOut_apply_mid`).
  Proof by cases on whether `(i, j)` lies in the middle block.
- `blockMat_conj_apply hA1 hA2 y y' hlk`: let `A` be upper triangular and zero on the middle
  block. Then `(blockMat y · A · blockMat y') k l = A k l` whenever `l ≤ k`. Proof: expand
  `(1 + P(y-1)Pᵀ) A (1 + P(y'-1)Pᵀ)`. The term with `PᵀAP` vanishes because `PᵀAP = 0`. Entry
  `(k, l)` of `P (y-1) (PᵀA)` is zero for `l ≤ k`: if `k` is in the middle, then
  `A (a + m) l = 0` for every `m`, because either `l` is also in the middle or `l < a ≤ a + m`.
  Entry `(k, l)` of `(AP) (y'-1) Pᵀ` is zero for `l ≤ k` by the symmetric argument.

### Smoothness and right derivatives of slices

- `contMDiff_sliceFactor`: `ν` is smooth on `GL_r(ℝ)` (from `contDiffAt_sliceFactor` and the
  Library's `contMDiff_of_contDiffOn`).
- `contDiff_blockMat`: `blockMat` is smooth. `contMDiff_comp_blockEmb`: `G ∘ ι` is smooth for
  smooth `G`.
- `midLin n a r`: the continuous linear map `y ↦ P y Pᵀ`, the derivative of the affine map
  `blockMat` (`hasFDerivAt_blockMat`).
- `rightDerivative_comp_blockEmb hG Z g` (**chain rule**):
  `R(Z) (G ∘ ι) (g) = R(P Z Pᵀ) G (ι g)`. Proof: by the Library's `rightDerivative_eq_fderiv`,
  both sides are derivatives of the extensions to matrices. Near `g`, the extension of `G ∘ ι`
  agrees with `y ↦ G̃(blockMat y)`. The chain rule gives `dG̃_{ι g}(P (g Z) Pᵀ)`, and
  `P (g Z) Pᵀ = ι(g) (P Z Pᵀ)` by `blockMat_mul_mid`.
- `slice_rightDerivative_mid hG Z` (**middle directions**):
  `σ_1 (R(P Z Pᵀ) G) = R(Z) (σ_1 G) - m · σ_1 G`, with `m = R(Z) ν (1)`. Proof: write
  `σ_1 G = ν · (G ∘ ι)`. The product rule
  (`RealPrincipalSeriesDuality.rightDerivative_mul_fun`) gives
  `R(Z)(σ_1 G) = R(Z)ν · (G ∘ ι) + ν · R(Z)(G ∘ ι)`. Since `ν(g g') = ν(g) ν(g')`, the Library's
  `rightDerivative_mul_left_of_eq` gives `R(Z)ν (g) = ν(g) m`. The chain rule identifies
  `ν · R(Z)(G ∘ ι)` with `σ_1 (R(P Z Pᵀ) G)`.
- `slice_rightDerivative_upper hχ hG hA1 hA2` (**upper triangular directions**): let `G` lie in
  the principal series of `χ` with `χ_i(e^x) = e^(τ_i x)`, and let `A` be upper triangular and
  zero on the middle block. Then `σ_1 (R(A) G) = (∑ᵢ αᵢ Aᵢᵢ) σ_1 G`, where
  `αᵢ = τᵢ + (n - 1)/2 - i`. Proof: at `g`, write `ι(g) A = C ι(g)` with
  `C = ι(g) A ι(g)⁻¹`. By `blockMat_conj_apply`, `C` is upper triangular with the same diagonal
  as `A`. `G` is exp-equivariant with exponents `α`
  (`RealBlockDerivative.isExpEquivariant_of_mem_principalSeries`). So
  `R(A) G (ι g) = dG̃_{ι g}(C ι(g)) = (∑ᵢ αᵢ Cᵢᵢ) G(ι g)` by
  `RealBlockDerivative.fderiv_upperTriangular_of_isExpEquivariant`.

### The curve `t ↦ exp(t W)`

- `expCurve W hW t`: for an antisymmetric real `W`, the orthogonal matrix `exp(t W)`
  (Mathlib's `NormedSpace.exp_mem_unitary_of_mem_skewAdjoint`). `expCurve_zero`: it is `1` at
  `t = 0`. `hasDerivAt_expCurve`: its entries have derivative `W i j` at `0`.

### The derivative defect of the induced map

Let `L' = pre ++ ds' ++ post`, `L = pre ++ ds ++ post`, and let `h`, `ha`, `hr`, `hr'`, `hn`,
`T`, `hT` be as in `RealInductionStagesInduce`.

- `lie_add`: `R(X + Y) = R(X) + R(Y)` on `KFin r ds`.
- `sliceK_one_apply_coe`: the underlying function of `σ_1 F` is `slice h 1 F`.
- `sliceK_lie_ind_skew W hW F` (**antisymmetric directions**):
  `σ_1 (R(W) (ind T F)) = T (σ_1 (R(W) F))`. Proof: fix `y ∈ GL_r(ℝ)`. Let `ℓ` be the functional
  `G ↦ (σ_1 G)(y)` on `KFin n L`, and `ℓ'` the functional `F ↦ (T σ_1 F)(y)` on `KFin n L'`.
  By `ind_kRep` and `sliceK_ind`, `ℓ(R(exp tW) ind T F) = ℓ'(R(exp tW) F)` for all `t`. The
  derivative axiom of `isRealGKModule_realStandardModule` for `L` and for `L'` computes the
  derivatives at `t = 0` of the two sides as `ℓ(R(W) ind T F)` and `ℓ'(R(W) F)`. These are
  equal by uniqueness of derivatives.
- `sliceK_one_lie_ind_sub_mem M hM X F`: `T (σ_1 (R(X) F)) - σ_1 (R(X) (ind T F)) ∈ M`. Proof:
  write `X = A + P Z Pᵀ + W` with `A = upperOut X`, `Z = midBlock X` and `W = skewOut X`. The
  defect is additive in `X` (`lie_add`).
  - For `A`, both slices are multiplied by the same scalar `∑ᵢ αᵢ Aᵢᵢ`. The exponents `αᵢ` of
    `L` and `L'` agree outside the middle (`realPositionExponent_outside`), and `Aᵢᵢ = 0` in
    the middle. With `σ_1 (ind T F) = T (σ_1 F)` (`sliceK_ind`), the defect is `0`.
  - For `P Z Pᵀ`, `slice_rightDerivative_mid` and `sliceK_ind` turn the defect into
    `T (R(Z) σ_1 F) - R(Z) (T σ_1 F)`, which lies in `M` by `hM`.
  - For `W`, the defect is `0` by `sliceK_lie_ind_skew`.
- `sliceK_ind_lie_sub_mem M hM X F κ` (**main theorem**):
  `σ_κ (ind T (R(X) F) - R(X) (ind T F)) ∈ M` for every `κ ∈ O(n)`. Proof: `σ_κ G = σ_1 (R(κ) G)`
  (`sliceK_kRep`). Also `R(κ) R(X) = R(κ X κᵀ) R(κ)` (`kRep_lie`) and
  `R(κ) ind T = ind T R(κ)` (`ind_kRep`). So the slice at `κ` of the defect for `(X, F)` is the
  slice at `1` of the defect for `(κ X κᵀ, R(κ) F)`. Then apply
  `sliceK_one_lie_ind_sub_mem`.
