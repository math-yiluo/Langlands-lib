# Heights on the split centre: proof of `RationalSplitCenterHeightStatement`

Module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSplitCenterHeightProof`.

## Result

`Langlands.HarishChandraSchwartz.rationalSplitCenterHeight : RationalSplitCenterHeightStatement.{u}`

The statement and its correspondence with Waldspurger (I.1 and VIII.4) are in
`RationalCentralProjection.md`. Fix a nonarchimedean local field `F`, a connected reductive `G`
over `F`, a split component `s : T → G` with image `A_G(F) = (rationalPoints.map s).range`, and a
closed matrix representation `ρ` with height `σ = rationalHeight ρ`. The theorem proves the two
clauses of the statement:

1. there is `C` with `1 + σ(a) ≤ C (1 + σ(a g))` for all `a ∈ A_G(F)` and
   `g ∈ G¹ = Plancherel.rationalCommonNormKernel G`;
2. for every Haar measure `μ_A` on `A_G(F)` there is `r₀` with
   `∫⁻ ofReal((1 + σ(a))^{-r₀}) dμ_A(a) < ∞`. The proof takes `r₀ = |I| + 1`, where `I` indexes
   the coordinates of the cocharacter lattice `X_*(T)`.

The proof adds no hypothesis. Every input is a published Library result imported by name.

## Notation

`valuation χ g` is the integer `H_χ(g)` with `|χ(g)|_F = q^{-H_χ(g)}`, for a rational character
`χ` of `G`. It is the `χ`-coordinate of `Plancherel.rationalCharacterValuation G g`. It is a
homomorphism in `g` (`valuation_mul`, `valuation_inv`) and vanishes on `G¹`
(`valuation_eq_zero_of_mem`). It is locally constant (`continuous_valuation`) because it factors
through the discrete valuation image (`Plancherel.continuous_rationalValuationImageProjection`).

## Helper results

All helpers are in the namespace `Langlands.HarishChandraSchwartz.SplitCenterHeight`.

- `zsmul_le_natAbs_mul` and `sum_zsmul_le`: let `τ` be a real function on an additive
  commutative group with `τ 0 = 0`, `τ (x + y) ≤ τ x + τ y` and `τ (-x) = τ x`. Then
  `τ (n • x) ≤ |n| τ x`, and `τ (∑ j, n j • b j) ≤ ∑ j, |n j| τ (b j)`. The proof is induction on
  `n` followed by `Finset.le_sum_of_subadditive`.
- `exists_abs_valuation_le`: for a closed `ρ` and a rational character `χ`, there is `C > 0`
  with `|H_χ(g)| ≤ C (1 + σ(g))` on `G(F)`. This is the Library's
  `MatrixRepresentation.rationalCharacter_abs_log_rationalMatrixNorm_bound`, which bounds
  `|log |χ(g)|_F|`. The bound is divided by `log q > 0` using
  `Plancherel.rationalNormLogarithm_spec` and `rationalNormLogarithm_eq_intValuation`.
- `valuation_map`: `H_χ(s(t)) = H_{χ ∘ s}(t)` for `t ∈ T(F)`
  (`Plancherel.rationalCharacterValuation_characterRestrict`).
- `map_mem_commonNormKernel`: `s` maps `T(F)¹` into `G¹`. This follows from `valuation_map`.
- `exists_splitCenter_comparison`: there are a finite type `I`, rational characters
  `χ_j` (`j ∈ I`) of `G` and constants `B, β ≥ 0` with the following two properties.
  - `σ(a) ≤ B + β ∑_j |H_{χ_j}(a)|` for every `a ∈ A_G(F)`.
  - If `H_{χ_j}(a) = 0` for every `j`, then `a ∈ G¹`.

### Proof of `exists_splitCenter_comparison`

`T` is a split torus (`hs.1.1.1`).

1. **Coordinates.** `IsSplitTorus.exists_cocharacterCoordinates` gives a linear equivalence
   `e : X_*(T) ≃ ℤ^I`. The pairing `X^*(T) × X_*(T) → ℤ` is perfect
   (`CocharacterUniformizer.latticePairing_isPerfPair`). So for each `k ∈ I` there is
   `α_k ∈ X^*(T)` with `⟨α_k, y⟩ = e(y)_k` for all `y`.
2. **Characters of `G`.** The restriction `X^*(G)_F → X^*(T)` has range of finite index `M ≠ 0`
   (`IsSplitComponent.finiteIndex_range_characterRestrict`). By `AddSubgroup.nsmul_index_mem`
   there are rational characters `χ_k` of `G` whose restrictions along `s` are `M • α_k`.
3. **Valuations on `A_G(F)`.** Write `ls` for the uniformizer lattice section
   `CocharacterUniformizer.latticeSection F T`, which sends `c` to `c(ϖ)`. By
   `CocharacterUniformizer.isUniformizerLatticeSection`, each `t ∈ T(F)` has some
   `c ∈ X_*(T)` with `t · ls(c)⁻¹ ∈ T(F)¹`. By `mem_normKernel_mul_section_inv_iff`, the valuation
   of `α_k` at `t` is then `⟨α_k, c⟩ = e(c)_k`. Hence `H_{χ_k}(s(t)) = M · e(c)_k` (`hval`).
4. **Height along the lattice.** Put `τ(y) = σ(s(ls(y)))` on `X_*(T)`. It satisfies
   `τ(0) = 0` and is subadditive and even, because `s ∘ ls` is a homomorphism and `σ` satisfies
   `rationalHeight_mul_le`, `rationalHeight_inv` and `rationalHeight_one`. Write `b` for the basis
   of `X_*(T)` obtained by transporting the standard basis along `e⁻¹`. By `sum_zsmul_le`,
   `τ(y) ≤ β₀ ∑_k |e(y)_k|` with `β₀ = ∑_k τ(b_k)`.
5. **The compact part.** `A_G(F) ∩ G¹` is compact
   (`isCompact_splitComponent_inf_commonNormKernel`), and `σ` is continuous
   (`continuous_rationalHeight`). So `σ ≤ B` there.
6. **Conclusion.** Write `t = (t · ls(c)⁻¹) · ls(c)`. The first factor maps into
   `A_G(F) ∩ G¹` by `map_mem_commonNormKernel`. Subadditivity of `σ` then gives
   `σ(s(t)) ≤ B + β₀ ∑_k |e(c)_k| = B + (β₀ / M) ∑_k |H_{χ_k}(s(t))|`.
   For the second property, suppose every `H_{χ_k}(s(t))` vanishes. Then `e(c) = 0`, because
   `M ≠ 0`. So `c = 0`, hence `t ∈ T(F)¹` and `s(t) ∈ G¹`.

## Proof of the theorem

Choose `χ_j`, `B` and `β` by `exists_splitCenter_comparison`. Choose `C_j` for each `χ_j` by
`exists_abs_valuation_le`, and put `Γ = ∑_j C_j`. Then `∑_j |H_{χ_j}(g)| ≤ Γ (1 + σ(g))` for all
`g ∈ G(F)` (`hsum`).

**Clause 1** holds with constant `1 + B + β Γ`. For `a ∈ A_G(F)` and `g ∈ G¹`, each
`H_{χ_j}(a g)` equals `H_{χ_j}(a)`. Therefore
`σ(a) ≤ B + β ∑_j |H_{χ_j}(a g)| ≤ B + β Γ (1 + σ(a g))`, and the inequality follows from
`σ(a g) ≥ 0` (`nlinarith`).

**Clause 2.** Fix a Haar measure `μ_A` on the subgroup `A_G(F)`. Let `Φ : A_G(F) → ℤ^I` be
`a ↦ (H_{χ_j}(a))_j`. It is continuous into a discrete space, hence measurable.

- **Majorant.** Let `r = |I| + 1` and let `v(λ)` be the vector of `ℝ^I` with integer coordinates
  `λ` (`Langlands.Global.Hecke.latticeVec` for the standard basis). Its sup norm is at most
  `∑_j |λ_j|`. Hence `1 + ‖v(Φ a)‖ ≤ (1 + Γ)(1 + σ(a))`, and
  `Langlands.Global.Hecke.rpow_neg_le_of_le_mul` gives
  `(1 + σ(a))^{-r} ≤ w(Φ a)`, where `w(λ) = (1 + Γ)^r (1 + ‖v(λ)‖)^{-r}`. The function `w` is
  summable over `ℤ^I` by `Langlands.Global.Hecke.summable_one_add_norm_latticeVec_rpow`, since
  `r > dim ℝ^I`.
- **Fibres.** Let `K` be the preimage of `A_G(F) ∩ G¹` in `A_G(F)`. It is compact by
  `Subtype.isCompact_iff` and `isCompact_splitComponent_inf_commonNormKernel`, so `μ_A(K) < ∞`.
  Each nonempty fibre `Φ⁻¹{λ}`, containing a point `a₀`, lies in the left translate `a₀ K`. The
  reason: `Φ(a₀⁻¹ a) = 0` and the second property of `exists_splitCenter_comparison`. Left
  invariance (`measure_preimage_mul`) then gives `μ_A(Φ⁻¹{λ}) ≤ μ_A(K)`.
- **Sum.** The chain of (in)equalities is
  `∫⁻ ofReal((1 + σ)^{-r}) dμ_A ≤ ∫⁻ ofReal(w ∘ Φ) dμ_A = ∑'_λ ofReal(w λ) μ_A(Φ⁻¹{λ})
  ≤ ofReal(∑'_λ w λ) · μ_A(K) < ∞`.
  It uses `lintegral_map`, `lintegral_countable'`, `Measure.map_apply`,
  `ENNReal.tsum_mul_right` and `ENNReal.ofReal_tsum_of_nonneg`.

## Relation to the publisher's sketch

The sketch in `RationalCentralProjection.md` uses a two-sided comparison of `σ` with `|H_G|` on
`A_G(F)`, obtained by diagonalizing `ρ ∘ s`. The implemented proof avoids diagonalization. Only
the upper bound `σ ≤ B + β ∑ |H_{χ_j}|` on `A_G(F)` is proved, by subadditivity along the
uniformizer lattice section and compactness of `A_G(F) ∩ G¹`; clause 1 needs no more. Clause 2
uses the opposite bound `|H_χ| ≤ C (1 + σ)`, which holds on all of `G(F)`. It also uses the fact
that the fibres of `Φ` are translates of subsets of `A_G(F) ∩ G¹`. The proof does not show that
`Φ` has image a full-rank lattice; the sum runs over all of `ℤ^I`.
