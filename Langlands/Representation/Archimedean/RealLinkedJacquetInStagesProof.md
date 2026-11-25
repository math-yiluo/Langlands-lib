# Induction in stages for the linked real Jacquet functional

Module: `Langlands.Representation.Archimedean.RealLinkedJacquetInStagesProof`.

## Result

`Langlands.Archimedean.realLinkedJacquetFunctionalInStages :
RealLinkedJacquetFunctionalInStagesStatement`.

The statement (module `RealLinkedJacquetPairReduction`) is as follows. Let `pre ++ core ++ post`
be a list of real blocks of total rank `n`, with `r = realRank core`. Let
`core' = core.map (realBlockTwist c)` be `core` twisted by `|det|^c`, with
`c = (realRank post - realRank pre)/2`. Suppose the `O(r)`-finite functions of the standard
module of `core'` carry a functional as in `RealLinkedJacquetFunctionalExists`. Then so do
the `O(n)`-finite functions of the standard module of `pre ++ core ++ post`.

`RealLinkedJacquetFunctionalExists n L` asks for a nonzero linear functional `ℓ` on the
`O(n)`-finite functions of the standard module of `L` and the following data. `ℓ` is a real
Jacquet functional (`IsRealJacquetFunctional`, Library `RealJacquetReduction`) with exponents
`a` and signs `e`: it kills the action of strictly upper triangular matrices and is an
eigenvector of every `E_jj` and every sign reflection `s_j`. There are also a position `p`
with `p + 1 < n` and `k : ℕ` such that `a_p - a_{p+1} = 1 - k` and
`ℓ(π(E_{p+1,p})^k v) = 0` for all `v`.

The functional for `pre ++ core ++ post` is `ℓ' ∘ Res`, with `Res F (g) = F(diag(1_a, g, 1))`
and `a = realRank pre`.

## Provenance

This is a step in the reduction `RealLinkedJacquetFunctionalReductionStatement`, which is
internal to the proof of `RealLinkedLanglandsQuotientNotLargeStatement`. The functional `f ↦ ℓ'(f(diag(1, ·, 1)))` on a representation induced
in stages is the usual passage of Jacquet functionals through parabolic induction. The twist
by `|det|^c` is the modulus character of the intermediate parabolic. The module makes no
literature claim beyond the theorem above.

The proof uses the modules `RealInductionStagesAverage`, `RealInductionStagesSlice`,
`RealInductionStagesFourier`, `RealInductionStagesInduce` and `RealInductionStagesDerivative`.
From these it takes the `O(r)`-finite spaces `KFin r L`, the actions `kRep` and
`lie r L X = realStandardLie r L (1 ⊗ X)`, the block embedding `ι = blockEmb h`, the slice
`sliceK h ha hr κ`, and the derivative formulas for slices. It also uses the modules
`RealBlockTestVector` and `RealSliceSurjective`.

## Declarations

All declarations except the main theorem are in the namespace
`Langlands.Archimedean.RealLinkedJacquetStages`.

### The factor `|det|^s`

- `detPow r s g = |det g|^s` on `GL_r(ℝ)`, with `abs_det_pos`, `ofReal_abs_det_ne_zero`,
  `detPow_add`, `detPow_zero`, `detPow_ne_zero`, `detPow_mul_detPow_neg`, `detPow_mul`,
  `detPow_of_abs_det_eq_one`, `detPow_of_mem_unitaryCompact`, `detPow_of_mem_upperUnipotent`,
  `detPow_diagonalUnits` and `contMDiff_detPow` (smoothness).
- `sliceFactor_eq_detPow`: the slice factor `sliceFactor` of `RealInductionStagesSlice` is `detPow r (-sliceExponent n a r)`.
- `contMDiff_mul_fun`: products of smooth functions on `GL_r(ℝ)` are smooth.
- `detPowMul r s`: multiplication by `|det|^s`, as a linear map. `detPowMul_apply`.

### Twisted lists of blocks

- `ofReal_abs_units_ne_zero`.
- `realPositionCharacter_map_twist`: the position characters of `ds.map (realBlockTwist s)`
  are those of `ds` times `|·|^s` (at positions `i < realRank ds`).
- `realInducedBlockAt_map_twist`: its induction blocks are those of `ds` with exponent
  shifted by `s` and the same weight.

### Twisting standard modules

- `blockFourierCoefficient_detPowMul`: block Fourier coefficients of `|det|^s f` are `|det|^s`
  times those of `f`.
- `detPowMul_mem_realStandardModule` (**twisting**): let `es` have the position characters of
  `ds` times `|·|^s`, and induction blocks of the weights of those of `ds`. Then `|det|^s`
  maps the standard module of `ds` into that of `es`.
- `detPowMul_mem_kFiniteVectors`: `|det|^s` preserves `O(r)`-finiteness.
- `twK hχ hind : KFin r ds →ₗ[ℂ] KFin r es`, the twist, with `twK_apply_coe`.
- `twist_char`, `twist_ind`: the hypotheses of `twK` for `ds` and its twist by `s`.
  `untwist_char`, `untwist_ind`: those for the twist and `ds`, with `-s`.

### Restriction to the middle block

Here `h : a + r ≤ n`, `ha : realRank pre = a`, `hr : realRank core = r` and
`hn : realRank (pre ++ core ++ post) = n`.

- `twistExp pre post = (realRank post - realRank pre)/2`, and
  `twisted pre core post = core.map (realBlockTwist (twistExp pre post))`.
  `realRank_twisted`.
- `sliceExponent_eq`: `sliceExponent n a r = twistExp pre post`.
- `res h ha hr : KFin n (pre ++ core ++ post) →ₗ[ℂ] KFin r (twisted pre core post)`, the
  restriction: the twist `twK` composed with the slice `sliceK h ha hr 1`.
- `res_apply`, `coe_res`: `Res F (g) = F(ι g)`.
- `res_lie_mid`, `res_pow_lie_mid`: `Res ∘ R(P Z Pᵀ)^k = R(Z)^k ∘ Res`, where
  `P = embMat n a r`.
- `res_lie_upper`: if `A` is upper triangular and zero on the middle block, then
  `Res ∘ R(A) = (∑ᵢ αᵢ Aᵢᵢ) Res`, with `αᵢ = τᵢ + (n - 1)/2 - i`. Here `τᵢ` is
  `realPositionExponent (pre ++ core ++ post) i`.
- `apply_blockEmb_mul_diagonalUnits`, `res_rep_apply`: for a diagonal orthogonal `κ = diag(t)`,
  `Res (ρ(κ) F) (g) = χ(t_out) Res F (g diag(t_mid))`.

### The Jacquet functional `ℓ' ∘ Res`

- `embMat_single_transpose`: `P E_{kl} Pᵀ = E_{ι k, ι l}`.
- `mid_midBlock_apply`: `P (Pᵀ X P) Pᵀ` is `X` on the middle block and `0` elsewhere.
- `principalSeriesCharacter_one'`, `outUnits_signVec_idx`, `midUnits_signVec_idx`,
  `outUnits_signVec_of_not_isMid`, `midUnits_signVec_of_not_isMid`: sign vectors split into
  their middle and outer parts.
- `resExp a r L a' i`: `a'_{i-a}` in the middle block and `αᵢ` outside.
  `resSign a r L e' i`: `e'_{i-a}` in the middle block, and outside `0` or `1` as
  `χ_{L,i}(-1)` is `1` or not. `resExp_idx`, `resSign_idx`, `neg_one_pow_resSign`.
- `res_sign_mid`: `Res ∘ ρ(s_{a+j}) = ρ(s_j) ∘ Res`.
- `res_sign_out`: `Res ∘ ρ(s_i) = χᵢ(-1) Res` for `i` outside the middle block.
- `isRealJacquetFunctional_comp_res`: if `ℓ'` is a real Jacquet functional on the twisted
  list with exponents `a'` and signs `e'`, then `ℓ' ∘ Res` is one on `pre ++ core ++ post`
  with exponents `resExp` and signs `resSign`.
- `exists_of_res_ne_zero` (**transfer**): if `ℓ'` with `a'`, `e'`, `p'`, `k` satisfies the
  conclusion of `RealLinkedJacquetFunctionalExists` for the twisted list and
  `ℓ' ∘ Res ≠ 0`, then `RealLinkedJacquetFunctionalExists n (pre ++ core ++ post)` holds, at
  the position `a + p'`.

### Surjectivity of the restriction

- `untwK hr : KFin r (twisted pre core post) →ₗ[ℂ] KFin r core`, multiplication by
  `|det|^{-c}`. `twK_untwK`: it is a right inverse of the twist in `res`.
- `res_surjective h ha hr hn`: `Res` is onto.

### Main theorem

- `Langlands.Archimedean.realLinkedJacquetFunctionalInStages`.

## Proof notes

`res_apply`. The slice factor is `|det g|^{-c}`, and the twist multiplies by `|det g|^c`.

`isRealJacquetFunctional_comp_res`. Let `X` be strictly upper triangular and `Z` its middle
block. Then `X = Xo + P Z Pᵀ`, where `Xo` is strictly upper triangular and zero on the middle
block. `res_lie_upper` gives `Res (R(Xo) F) = 0`, since the diagonal of `Xo` is `0`.
`res_lie_mid` gives `Res (R(P Z Pᵀ) F) = R(Z) Res F`, which `ℓ'` kills because `Z` is
strictly upper triangular. For `E_jj` in the middle block, `E_jj = P E_{j'j'} Pᵀ` and the
eigenvalue is `a'_{j'}`. Outside the middle block, `res_lie_upper` with `A = E_jj` gives
`αⱼ`. The sign reflections are handled in the same way by `res_sign_mid` and `res_sign_out`.

`exists_of_res_ne_zero`. Take the position `a + p'`. The exponent condition holds by
`resExp_idx`. The vanishing condition holds because
`E_{a+p'+1, a+p'} = P E_{p'+1,p'} Pᵀ` and `res_pow_lie_mid`.

`res_surjective`. Given `f`, `RealSliceSurjective.sliceK_one_surjective` gives `F` with
`σ₁ F = untwK f`. Then `Res F = twK (untwK f) = f` by `twK_untwK`.

`realLinkedJacquetFunctionalInStages`. Take `ℓ'` from the hypothesis, with `a = realRank pre`
and `r = realRank core`. Then `a + r ≤ n`. Since `Res` is onto, `ℓ' ∘ Res = 0` would force
`ℓ' = 0`. So `ℓ' ∘ Res ≠ 0`, and `exists_of_res_ne_zero` concludes.
