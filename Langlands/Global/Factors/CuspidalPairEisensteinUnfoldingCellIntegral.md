# Unfolding the generic coefficient cell by cell

Module `Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingCellIntegral` (namespace
`Langlands.Global.CuspidalPairEisenstein.Unfolding`) unfolds the contribution of each cell `J`
to the generic coefficient. It then proves that every cell other than the open cell contributes
zero. This is the analogue for the two-block parabolic of `GL_N`, `N = r + t + 2`, of Shahidi,
*Functional equation satisfied by certain L-functions*, Compositio Math. 37 (1978), proof of
Lemma 2.1, pp. 181–182, which treats a maximal parabolic subgroup of split `G₂`: the
unfolding of each double coset in (2.10.2), and the vanishing of the non-open classes in the
paragraph after (2.10.3). The source works with the right quotient
`G_F/P_F`, and the Library with the left quotient `P(F) \ GL_N(F)`, which corresponds to it
under inversion `g ↦ g⁻¹`.

## An abstract integrability criterion

`integrableOn_iUnion_of_tsum_le`: let `μ` be a left invariant measure on a group `H`, `s` a
measurable strict fundamental domain of finite measure for a subgroup `Γ`, and `ρ i` a countable
family of representatives of `Λ \ Γ` for a subgroup `Λ ≤ Γ`. Let `f` be measurable, and assume
that for every `x` the family `i ↦ ‖f(ρ i x)‖` is summable with `∑' i ‖f(ρ i x)‖ ≤ B`. Then `f`
is integrable on `⋃ i, ρ i • s`. The summability hypothesis cannot be dropped, because in Lean
the sum `∑'` of a nonsummable family is `0`. The translates are disjoint
(`RankinSelbergGlobal.Unfolding.pairwise_disjoint_smul`), so the lintegral over the union is
`∫_s ∑' i ‖f(ρ i x)‖ ≤ B μ(s)`.

## The generic character

`genericChar ψ x = ψ(x_(0,1) + ⋯ + x_(N-2,N-1))` on `N₀(𝔸)`, for an additive character
`ψ : 𝔸 → ℂ`. For every such `ψ` it is multiplicative (`genericChar_mul`). Each further
property is proved under the corresponding assumption on `ψ`:

- `continuous_genericChar`: it is continuous when `ψ` is continuous.
- `genericChar_ratHom`, `genericChar_of_mem_Γ₀`: it is trivial on `N₀(F)` when `ψ` is trivial
  on `F`.
- `norm_genericChar`: it has norm one everywhere when `‖ψ(a)‖ = 1` for every `a ∈ 𝔸`.

A standard additive character (`IsStandardAdditiveCharacter F ψ`: continuous, nontrivial,
trivial on `F` and of norm one) satisfies all three assumptions. Below, `unfold_cell` and
`setIntegral_cellIntegrand_eq_zero` assume a standard `ψ`. `continuous_cellIntegrand` assumes
only that `ψ` is continuous. `cellTerm_mul_conj` and `cellIntegrand_patternRational_mul`
assume only that `ψ` is trivial on `F`.

## Unfolding one cell

- `cosetRep J q = δ_q ∈ N₀(F)`, the chosen representatives of `Λ_J(F) \ N₀(F)`, with
  `existsUnique_cosetRep`. `countable_stabilizerCosets`: there are countably many.
- `cellIntegrand φ s ψ J x = φ_s(γ_J x) · conj(ψ_N(x))`, the unfolded integrand, and
  `continuous_cellIntegrand`. `cellTerm_mul_conj`: the term of cell `J` at `q`, multiplied by
  `conj(ψ_N(x))`, is `cellIntegrand J (δ_q x)`.
- `fd₀ F n` is the Library's fundamental domain of `N₀(F)` in `N₀(𝔸)`, and
  `cellDomain J = ⋃_q δ_q · fd₀` is a measurable fundamental domain of `Λ_J(F)`
  (`measurableSet_cellDomain`, `existsUnique_mem_cellDomain`). `haar_fd₀_ne_top`: `fd₀` has
  finite Haar measure.
- `unfold_cell` (**unfolding one cell**): for `σ < Re s` (with `NormalBound φ σ`) and standard
  `ψ`, `cellIntegrand J` is integrable on `cellDomain J`, the cell's part of the series times
  `conj(ψ_N)` is integrable on `fd₀`, and
  `∫_{fd₀} (∑'_q cellTerm φ s J q (x)) conj(ψ_N(x)) dx = ∫_{cellDomain J} cellIntegrand J`.
  The integrability comes from `integrableOn_iUnion_of_tsum_le` with the bound of
  `cellTerm_fiber_le` and `exists_bound_unipotent`. The identity is the Library's
  `RankinSelbergGlobal.Unfolding.integrableOn_tsum_and_setIntegral_eq`.

## The non-open cells vanish

- `cellIntegrand_patternRational_mul`: `cellIntegrand J` is left invariant under `Λ_J(F)`. For
  `δ ∈ Λ_J(F)`, `γ_J δ = (γ_J δ γ_J⁻¹) γ_J` with `γ_J δ γ_J⁻¹ ∈ P(F)`
  (`permutation_conj_mem_parabolic`), and `ψ_N(δ) = 1`.
- `setIntegral_cellIntegrand_eq_zero` (**non-open cells**): for a section `φ`, a standard
  additive character `ψ` and `J ≠ J₀`, `∫_{cellDomain J} cellIntegrand J = 0` whenever the
  integrand is integrable there. By
  `exists_simpleRoot_of_ne_openPivots` there is `k` with `k ∉ J`, `k + 1 ∈ J`. Since `ψ` is
  nontrivial, there is `y₀` with `ψ(y₀) ≠ 1`. Let `v₀ = 1 + y₀ E_(k,k+1) ∈ Λ_J(𝔸)`. For
  `n ∈ Λ_J(𝔸)`, the element `γ_J n v₀ n⁻¹ γ_J⁻¹` lies in `U(𝔸)`
  (`permutation_conj_rootElement_mem`), and `φ_s` is left `U(𝔸)`-invariant. Also
  `ψ_N(n v₀ x) = ψ_N(n) ψ(y₀) ψ_N(x)` (`sum_superdiag_rootElement`). Hence
  `cellIntegrand J (n v₀ x) = conj(ψ(y₀)) · cellIntegrand J (n x)`. The vanishing criterion
  `setIntegral_eq_zero_of_mul_right`
  ([CuspidalPairEisensteinUnfoldingVanishing.md](CuspidalPairEisensteinUnfoldingVanishing.md))
  applies with `N = Λ_J(𝔸)`, `Λ = Λ_J(F)` and Haar measure on `Λ_J(𝔸)`. That measure is
  bi-invariant and gives the fundamental domain of `Λ_J(F)` finite positive mass, by
  [CuspidalPairEisensteinUnfoldingGroups.md](CuspidalPairEisensteinUnfoldingGroups.md).

The vanishing argument uses the left `U(𝔸)`- and `P(F)`-invariance of `φ_s`, the continuity of
`φ_s` (for the measurability of the integrand), the standard additive character `ψ` (it is
continuous, trivial on `F` and nontrivial) and the integrability of `cellIntegrand J` on
`cellDomain J`, which `unfold_cell` supplies. It does not use the cuspidality of the inducing
data. This is the vanishing in Shahidi's paragraph after (2.10.3), p. 182, where the inner
integral over `V_𝔸 / V_F` factors through a character integral over `(V_w)_𝔸 / (V_w)_F`; see
[CuspidalPairEisensteinUnfoldingCells.md](CuspidalPairEisensteinUnfoldingCells.md) for the
comparison.
