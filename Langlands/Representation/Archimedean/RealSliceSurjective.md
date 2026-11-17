# The slice at the identity is surjective

Module: `Langlands.Representation.Archimedean.RealSliceSurjective`.

## Purpose and provenance

This module is internal infrastructure for the proof of
`Langlands.Archimedean.RealLinkedJacquetFunctionalInStagesStatement` (module
`RealLinkedJacquetInStagesProof`). There it gives the nonvanishing of `ℓ' ∘ Res`.

Let `pre`, `ds`, `post` be lists of real blocks, with `a = realRank pre`, `r = realRank ds`,
`a + r ≤ n` and `n = realRank (pre ++ ds ++ post)`. Worker 109's slice at the identity
(module `RealInductionStagesSlice`) is

`sliceK h ha hr 1 : KFin n (pre ++ ds ++ post) →ₗ[ℂ] KFin r ds`,
`σ₁ F (g) = ν(g) F(ι g)`,

where `ι = blockEmb h` is `g ↦ diag(1_a, g, 1)` and `ν = sliceFactor n a r` is a power of
`|det g|`. Here `KFin m L` is the space of `O(m)`-finite functions of the real standard module
of `L` on `GL_m(ℝ)` (`InductionStages.KFin`). The main result, `sliceK_one_surjective`, says
that `σ₁` is onto.

This is the function-level form of a standard fact: restriction to the Levi factor maps an
induced representation onto the representation it was induced from. The module proves only
the statements listed below and makes no other literature claim.

All declarations are in the namespace `Langlands.Archimedean.RealSliceSurjective`.
`IsMid a r i` (`a ≤ i < a + r`), `idx h j = a + j`, `midBlock n a r κ` (the middle `r × r`
block of `κ`), `blockMat`, `kRep`, `ind` and `sliceK_ind` are Worker 109's
(`RealInductionStagesSlice`, `RealInductionStagesAverage`, `RealInductionStagesInduce`).
`zp`, `zm`, `bf`, `IsSignEq` and `exists_KF` are from `RealBlockTestVector`.

## Declarations

### Expanding induction blocks into characters

- `charList ds`: `ds` with every induction block `.induced d` of weight `m` and exponent
  `t` replaced by the two character blocks `charData ((|m| + 1) mod 2) (t + |m|/2)` and
  `charData 0 (t - |m|/2)`. These carry the two position characters
  `sgn^{|m|+1} |·|^{t+|m|/2}` and `|·|^{t-|m|/2}` of the induction block.
- `realRank_charList`: the rank does not change.
- `realInducedBlockAt_charList`: `charList ds` has no induction blocks.
- `pow_mod_two_eq`, `sign_sq`: `y^{m mod 2} = y^m` when `y² = 1`; `(x/|x|)² = 1`.
- `realPositionCharacter_charList`: `charList ds` and `ds` have the same position
  characters at every position.
- `realStandardModule_le_charList`, `kFin_le_charList`: the standard module of `ds` lies in
  that of `charList ds`, and so do their `O(r)`-finite parts. The standard module of `ds` is
  the principal series of the position characters cut out by vanishing conditions at the
  induction blocks. `charList ds` has the same principal series and no conditions.

### An equivariant retraction

- `incl ds : KFin r ds →ₗ[ℂ] KFin r (charList ds)`: the inclusion. `incl_kRep`: it commutes
  with `O(r)`.
- `exists_retraction ds`: there is `T : KFin r (charList ds) →ₗ[ℂ] KFin r ds` that commutes
  exactly with the action `kRep` of `O(r)` and satisfies `T (incl ds f) = f`. `T` is the
  `O(r)`-average (`InductionStages.avg`) of a linear left inverse `T0` of `incl`.

### Sign averages of polynomials

- `sv u`, `wt q u`: for `u : Fin r → ℤˣ`, the real sign vector of `u` and the weight
  `∏ⱼ uⱼ^{qⱼ}`. `sv_mul`, `wt_mul`, `wt_one`, `wt_mul_self` (`wt q u ^ 2 = 1`).
- `pev P Y`: evaluation of `P : MvPolynomial (Fin r × Fin r) ℂ` at the entries of a real
  matrix `Y`.
- `pt q P Y = ∑ᵤ wt q u · P(diag(u) Y)`, the sign average.
- `pt_diagonal`, `pt_diagonal'`: `pt q P (diag(s) Y) = (∏ⱼ sⱼ^{qⱼ}) pt q P Y` for sign
  vectors `s` (given as `sv v` or as a real `±1` vector). `unitsOf`, `sv_unitsOf`,
  `wt_unitsOf` convert between the two forms.
- `realUnits`, `coe_realUnits`, `sv_mul_self`, `diagonal_sv_mem` (`diag(u)` is orthogonal),
  `principalSeriesCharacter_realUnits`.
- `pt_eq` (**the sign average on `O(r)`**): let `ψ` lie in the principal series of
  characters `χⱼ` with `χⱼ(1) = 1` and `χⱼ(-1) = (-1)^{qⱼ}`, and let `P` agree with `ψ` on
  `O(r)`. Then `pt q P k = 2^r ψ(k)` for `k ∈ O(r)`. (The count appears as
  `Fintype.card (Fin r → ℤˣ)`.)

### Translate-finiteness and continuity of sums, products and polynomials

- `isTranslateFinite_finset_prod`, `isTranslateFinite_finset_sum`: finite products and sums of
  translate-finite functions are translate-finite.
- `isTranslateFinite_eval`: a polynomial in translate-finite functions is translate-finite.
- `continuous_eval_comp`: a polynomial in continuous functions is continuous.

### Positions of induction blocks

- `sgnExp L i`: `0` if `χ_{L,i}(-1) = 1` and `1` otherwise, for the position character
  `χ_{L,i} = realPositionCharacter L i`. `neg_one_pow_sgnExp`: `(-1)^{sgnExp L i} = χ_{L,i}(-1)`.
- `induced_succ`: if an induction block `d` starts at `p`, then none starts at `p + 1`, and
  the position characters at `p` and `p + 1` are `realInducedFirstCharacter d` and
  `realInducedSecondCharacter d`.
- `sgnExp_succ_of_some`: then `sgnExp L (p + 1) = 0`.
- `realInducedFirstCharacter_neg_one`: `realInducedFirstCharacter d (-1) = (-1)^{|m|+1}`.

### The test function

Fix `L`, `a`, `r` and `P : MvPolynomial (Fin r × Fin r) ℂ`.

- `gFac L a r i κ`, the factor of row `i`. If an induction block of weight `m` starts at `i`
  (and `i + 1 < n`), it is the block factor `bf` of degree `|m| + 1` with `c = c' = i`.
  Otherwise it is `1` in the middle block and the sign power `κᵢᵢ^{sgnExp L i}` outside.
  `gExp L a r i` is its sign exponent: `|m| + 1`, `0` or `sgnExp L i`.
- `mExp L a r i`: `sgnExp L i` in the middle block and `0` outside.
- `ptMid L a r P κ = pt (j ↦ sgnExp L (a + j)) P (midBlock n a r κ)`.
- `testFun L a r P κ = (∏ᵢ gFac L a r i κ) · ptMid L a r P κ`.
- `gFac_of_none`, `gFac_of_some`, `gFac_ia`, `gExp_of_none`, `gExp_of_some`: unfolding.
  `lt_of_some`: an induction block starting at `i` has `i + 1 < n`.
- Signs: `gFac_diag`, `midBlock_diagonal_mul`, `isSignEq_ptMid`, and `isSignEq_testFun`
  (`IsSignEq (gExp + mExp) testFun`). `neg_one_pow_exp`: if no induction block meets the
  middle block, `(-1)^{gExp i + mExp i} = χ_{L,i}(-1)` for every `i`.
- Rotations: `not_isMid_ia`, `midBlock_rot`, `gFac_rot_of_ne`, and `testFun_rot`. The last
  says that under the rotations of an induction block of weight `m` outside the middle,
  `testFun` has exactly the two modes `±(|m| + 1)`. `abs_lt_natAbs_succ`: `|k| < |m|`
  implies `|k| < |m| + 1`. `coeff_testFun`: the block Fourier coefficients of `testFun` of
  weight `|k| < |m|` vanish at such a block.
- Continuity and translate-finiteness: `continuous_gFac`, `isTranslateFinite_gFac`,
  `ptMid_eq` (`ptMid` as an explicit sum of polynomials in the entries), `continuous_testFun`,
  `isTranslateFinite_testFun`.
- Values on the middle block: `midBlock_blockMat`, `gFac_blockMat`
  (`gFac i (blockMat y) = gFac i 1`), `gFac_one_ne_zero`, and `testFun_blockMat`
  (`testFun (blockMat y) = (∏ᵢ gFac i 1) · pt P y`).

### Surjectivity

- `sliceK_one_surjective_of_none` (`h`, `ha`, `hr`, `hn`, and
  `hM : ∀ p, realInducedBlockAt M p = none`): if the middle list `M` has no induction
  blocks, `sliceK (post := post) h ha hr 1` is surjective.
- `sliceK_one_surjective` (`h`, `ha`, `hr`, `hn`): **the slice at the identity is onto**,
  `Function.Surjective (sliceK (post := post) h ha hr 1)` for every middle list `ds`.

## Proof notes

`sliceK_one_surjective_of_none`. Let `ψ ∈ KFin r M`. Induction blocks of
`L = pre ++ M ++ post` lie in `pre` or `post` (`realInducedBlockAt_append_cases`), so they do
not meet the middle block. The Library's
`OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors` gives a polynomial `P`
in the matrix entries that agrees with `ψ` on `O(r)`. The function `testFun L a r P` meets the
hypotheses of `exists_KF`, which gives `v ∈ KFin n L` equal to `testFun` on `O(n)`. On
`k ∈ O(r)`, the slice factor is `1`, `ι k = blockMat k`, and `testFun_blockMat` with `pt_eq`
gives `σ₁ v (k) = c₀ ψ(k)`, where `c₀ = (∏ᵢ gFac i 1) · 2^r ≠ 0`. Both `σ₁ v` and `c₀ ψ` lie
in the same principal series, so they are equal
(`eq_of_eqOn_unitaryCompact_of_mem_principalSeries`). Then `σ₁ (c₀⁻¹ v) = ψ`.

`sliceK_one_surjective`. Let `ψ ∈ KFin r ds`. Apply the previous case to `M = charList ds`
and `incl ds ψ`, which gives `G` with `σ₁ G = incl ds ψ`. Take the retraction `T` of
`exists_retraction`. Worker 109's `ind h ha hr hr' hn T hT G` lies in
`KFin n (pre ++ ds ++ post)`, and `sliceK_ind` gives `σ₁ (ind T G) = T (σ₁ G) = T (incl ψ) = ψ`.
