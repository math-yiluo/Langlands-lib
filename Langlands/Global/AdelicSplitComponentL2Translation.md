# Translated Harish-Chandra components on weighted `L²`

Module `Langlands.Global.AdelicSplitComponentL2Translation`. Main results:
`Langlands.Global.StandardParabolicFamily.translatedComponent_of_operators` (for given constant-term
operators) and `Langlands.Global.StandardParabolicFamily.exists_translatedComponent`. Its statement form is
`Langlands.Global.TranslatedComponentStatement`, proved by `Langlands.Global.translatedComponent`.

## Statement

Let `𝓕 : StandardParabolicFamily F G` be a compatible standard parabolic family over a number
field `F`, in an arbitrary universe. The ingredients are:

- `W : G(𝔸) → [0, ∞]` is a measurable weight, left-invariant under the image `Λ₀` of `P₀(F)` and
  under every standard unipotent group `U_J(𝔸)`, `J ⊆ Δ₀`.
- `μ_W = weightedHaar W` is `W` times Haar measure restricted to the Borel fundamental domain `D₀`
  of `Λ₀`.
- `P` is a finset of characters, `J = P ∩ Δ₀` (`finsetIndex P`), and `a` is an adelic point of the
  split component `A_J`, with image `b = a ≫ (a_J ≫ l_J ≫ p_J)` in `G(𝔸)`.
- `κ < ∞` satisfies `W(g) ≤ κ W(b g)` for all `g`.

Then there are the following:

1. Contractions `T S` of `L²(μ_W)` (one for each finset `S`) with `T Δ₀ = id`. `T S Fn` agrees
   almost everywhere with `componentFoldCT S f` for every measurable representative `f` of `Fn`.
   This is `exists_componentOperators` of `AdelicL2HarishChandraDecomposition`.
   `componentFoldCT S f` is the folded constant term of `f` along `U_{S ∩ Δ₀}`.
2. A continuous linear operator `L` on `L²(μ_W)`, with
   `‖L‖ ≤ ((κ · c(b))^{1/2}).toReal · 2^{|P|}`,
   where `c(b) = mulEquivHaarChar (conjPoints b)` is the Haar scaling factor of conjugation by `b`
   on `U_J(𝔸)`. For every `Fn` and measurable representative `f`,
   `L Fn = (g ↦ Σ_{S ⊆ P} (−1)^{|P ∖ S|} componentFoldCT S f (b g))` almost everywhere.

So `L` is the raw (unnormalized) operator "translate by `b` after the Harish-Chandra component
`Σ_{S ⊆ P} (−1)^{|P ∖ S|} T S`". No modulus factor is applied to its output.

## Proof

- `setLIntegral_enorm_sq_splitComponent_le`: for `f` measurable and invariant under `Λ₀` and
  `U_J(𝔸)`, `∫_{D₀} ‖f(b g)‖² W ≤ κ c(b) ∫_{D₀} ‖f‖² W`. Bound `W(g)` by `κ W(b g)` and apply the
  split-component translation formula (`AdelicSplitComponentCentralizer`) to `‖f‖² W`.
- `foldConstantTerm_standard_invariant`: the adelic instance of `FundamentalDomainConstantTermInvariance`.
  The folded constant term along `U_J` is invariant under `Λ₀` and `U_J(𝔸)` at every point. The
  hypotheses are supplied exactly as in `AdelicStandardConstantTermOperator`.
- `componentFoldCT_invariant`: for `S ⊆ P`, `U_{P ∩ Δ₀} ≤ U_{S ∩ Δ₀}` by the standard parabolic
  order. So `componentFoldCT S f` is invariant under `U_J(𝔸)`, and the representative
  `Σ_{S ⊆ P} ± componentFoldCT S f` of the component is invariant under `Λ₀` and `U_J(𝔸)`.
- `coeFn_finset_sum_ae` and `alternatingSum_apply_ae`: finite sums and alternating sums of operators
  in `L²` are computed almost everywhere on representatives.
- `translatedComponent_of_operators` takes given contractions `T S` with the folded-constant-term
  formula as input, so that the same `T` can be used for several translations. It applies
  `InvariantTranslation.translateCLM` (module
  `Langlands.Analysis.InvariantTranslationOperator`) with these ingredients:
  - the invariance class `P` = invariance under `Λ₀` and `U_J(𝔸)`;
  - the operator `T` = the alternating sum, which has norm at most `2^{|P|}`;
  - the constant `K = κ c(b)`.

  `exists_translatedComponent` combines it with `exists_componentOperators`.

## Provenance

Joseph Bernstein and Erez Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §6.2 (equation (6.2), p. 201),
§7.5 (p. 219) and §7.6 (pp. 219–220). The system uses `D_α(s)(T_{a_α}) f_P` on the Siegel domain.

**Normalization.** The operator `L` of this module is the *raw* (unnormalized) left shift by `b`
after the component, `f ↦ (g ↦ f_P(b g))`, with no scalar on the output. The Haar factor `c(b)`
enters only the norm bound. For `b = a_α` this is the source's `τ_α` applied to `f_P`, not
`T_{a_α} f_P`. In (6.2) `T_a` is the twisted shift `T_a φ(g) = δ_P(a)^{−1/2} φ(a g)`. On p. 219
the source compares the two: `τ_α = δ_P(a_α)^{1/2} T_{a_α}`. So on the `P`-component
`T_{a_α} = δ_P(a_α)^{−1/2} τ_α`. Here `δ_P(a_α) = δ_{P_α}(a_α)`, since `a_α` is central in
`M_{P_α}`.

The published target `Langlands.Global.UniformGrowthLocalFinitenessStatement` already uses plain
left translation. Its Markdown (section "Correspondence with the source", item "Twisted action")
rescales each monic polynomial: `D_α(s)(T_{a_α}) = κ^m D̃_α(s)(L_{a_α})`, with
`κ = δ_{P_α}(a_α)^{−1/2}`. So the raw building block is the one needed there.

For split-component points with dominant height, the Siegel weight `W = 1_S e^{−2⟨λ, H₀⟩}`
satisfies `W ≤ e^{2⟨λ, H₀(b)⟩} W(b ·)`. This module provides the bounded raw operators
"translate by `b` after `f ↦ f_P`" on the weighted `L²` space of a fundamental domain of `P₀(F)`.
It does not construct the polynomial operators, does not prove the §7.5 estimates, and does not
verify the weight inequality for a specific weight.
