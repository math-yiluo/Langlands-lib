# Local bases and the vanishing of `X⁺` (Waldspurger, proof of Proposition VI.4.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.WavePacketPositivePartVanishing`,
namespace `Langlands.HarishChandraSchwartz`. It imports only Mathlib:
`LinearMap.exists_antilipschitzWith`, `LinearIndependent.eventually`,
`LinearIndependent.span_eq_top_of_card_eq_finrank'`, `finrank_span_eq_card`,
`Submodule.mem_span_range_iff_exists_fun`, `inner_self_eq_norm_mul_norm`, `norm_inner_symm`,
`IsCompact.induction_on`, `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`,
`norm_integral_le_of_norm_le`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. The quotes were checked on the rendered PDF pages 73 and 74.

Proof of Proposition VI.4.1, printed pp. 307–309 (PDF pp. 73–75):

- p. 307: `f_ψ^{(P')}(m') = X^w + X^+` (3), where
  "`X^+ = δ_{P'}(m')^{1/2} lim_{n→∞} δ_{P'}(a)^{−n/2} ∫_𝒪 µ(ω)(E^G_P ψ_{n,ω})^+_{P̄'}(a^{−n}) dω`,
  pour peu que ces limites existent", with `a ∈ A_{M'}` such that `|α(a)|_F < 1` for every
  `α ∈ Σ(P')`.
- p. 308: "(4) il existe `ε > 0`, `C > 0`, et `d ∈ ℕ` tels que pour tout `n ∈ ℕ` tout `ω ∈ 𝒪`,
  on ait l'inégalité `|(E^G_P ψ_{n,ω})^+_{P̄'}(a^{−n})| ⩽ C δ_{P'}(a)^{n/2}(1 + σ(a^n))^d
  e^{−ε|H_0(a^n)|}`. Comme `𝒪` est compact, il suffit de prouver que pour `ω₀ ∈ 𝒪`, on a une
  telle majoration dans un voisinage convenable de `ω₀`. Fixons `ω₀ ∈ 𝒪` et un ensemble fini
  `ℱ ⊂ C^∞(𝒪, P)^{H×H}`, formé de fonctions rationnelles régulières, tel que
  `{ψ'_{ω₀} ; ψ' ∈ ℱ}` soit une base de `L(ω₀, P)^{H×H}`. Il existe un voisinage `𝒰` de `ω₀`
  dans `𝒪` tel que, pour tout `ω ∈ 𝒰`, `{ψ'_ω ; ψ' ∈ ℱ}` soit encore une base de
  `L(ω, P)^{H×H}`. […] Quitte à restreindre `𝒰`, on peut supposer qu'il existe `C₁ > 0`, tel que
  pour tout `ψ'' ∈ C^∞(𝒪; P)^{H×H}` et tout `ω ∈ 𝒰`, on ait l'inégalité
  `Σ_{ψ' ∈ ℱ} |C(ψ', ψ'', ω)| ⩽ C₁ sup{|(ψ'_ω, ψ''_ω)| ; ψ' ∈ ℱ}`". Then, from Lemma VI.2.3
  (`|(E^G_P ψ'_ω)^+_{P̄'}(m)| ⩽ C₂ Ξ^{M'}(m) e^{−ε|H_0(m)|}`), the inequality (5)
  `|(E^G_P ψ_{n,ω})^+_{P̄'}(a^{−n})| ⩽ C₁C₂ e^{−ε|H_0(a^n)|} sup{|(ψ'_ω, ψ_{n,ω})| ; ψ' ∈ ℱ}`.
- p. 309: from Lemmas VI.2.2 and II.1.1, `|(ψ'_ω, ψ_{n,ω})| ⩽ C₄ δ_0(a)^{n/2}(1 + σ(a^n))^d`
  with `δ_0(a) = δ_{P'}(a)`, which with (5) proves (4); "On déduit de (4) l'égalité `X^+ = 0`."

The abstraction, the hypotheses and the proof route are internal to this project.

## Relation to the source

- The parameter space `X` (with the topology and the measure `μ`) is the orbit `𝒪`; `w` is the
  density `µ(ω)` (integrable on the compact orbit). `E` is one finite-dimensional inner product
  space standing for all the spaces `L(ω, P)^{H×H}`, `ω ∈ 𝒪`, with the hermitian product of V.2;
  the source's spaces depend on `ω`, and their identification with one space (as in a compact
  realization) is not part of this module.
- `ψ n ω ∈ E` are the vectors `ψ_{n,ω}`; `ℓ n ω : E →ₗ[ℂ] ℂ` are the linear forms
  `v ↦ (E^G_P v)^+_{P̄'}(a^{−n})`; `b ω i` (with `i : Fin k`) are the values `ψ'_ω` of the
  regular rational sections `ψ' ∈ ℱ`. Continuity of `b` at `ω₀`, and the property that the
  `b ω₀ i` form a basis, are hypotheses.
- `t n`, `s n`, `h n` stand for `δ_{P'}(a)^{n/2}`, `σ(a^n)` and `|H_0(a^n)|`; the hypotheses
  `s n ≤ A n` and `B n ≤ h n` with `B > 0` hold for these (`σ(a^n) ≤ n σ(a)`,
  `|H_0(a^n)| = n |H_0(a)|` with `H_0(a) ≠ 0`), but this is not formalized here.
- The decay bound for the `ℓ n ω (b ω i)` (Lemma VI.2.3 at `m = a^{−n}`) and the bound for the
  inner products (Lemmas VI.2.2 and II.1.1 together with the identity
  `(ψ'_ω, ψ_{n,ω}) = mes(H ∩ U')(ψ'_ω, ρ₁(a^n)ρ₂(m'^{−1})ψ_ω)`) are hypotheses.
- The conclusion of `tendsto_inv_smul_integral_of_local_basis` is the vanishing of the limit
  defining `X^+` (up to the constant factor `δ_{P'}(m')^{1/2}`). The source's limit runs over
  `n ⩾ N`; this does not affect the limit.

## Contents

### Coefficients near a basis

Section variables for the first result: `𝕜` a nontrivially normed complete field, `E` a normed
space over `𝕜`, `ι` a finite type (`[Fintype ι]`); families `ι → E` carry the product topology.

- `exists_norm_le_norm_sum_smul_of_linearIndependent`: for `f : ι → E` with
  `hf : LinearIndependent 𝕜 f`, there is `C > 0` such that for all `g` in a neighbourhood of `f`
  and all `c : ι → 𝕜`, `‖c‖ ≤ C * ‖∑ i, c i • g i‖` (`‖c‖` the sup norm).

Further results with `𝕜` an `RCLike` field, `E` an inner product space over `𝕜`, `ι` finite:

- `exists_sum_norm_le_sum_norm_inner_of_linearIndependent`: for `f` with
  `hf : LinearIndependent 𝕜 f`, there is `C ≥ 0` such that for all `g` near `f` and all `c`,
  `∑ i, ‖c i‖ ≤ C * ∑ j, ‖inner 𝕜 (g j) (∑ i, c i • g i)‖` (the constant `C₁`, with the sum over
  `j` in place of the supremum).
- `exists_norm_apply_le_of_linearIndependent`: for a normed space `F` over `𝕜` and `f` with
  `hf : LinearIndependent 𝕜 f`, there is `C ≥ 0` such that for all `g` near `f`, every linear map
  `ℓ : E →ₗ[𝕜] F`, every `B : ℝ` with `∀ i, ‖ℓ (g i)‖ ≤ B` and every
  `w ∈ Submodule.span 𝕜 (Set.range g)`: `‖ℓ w‖ ≤ C * B * ∑ j, ‖inner 𝕜 (g j) w‖` (the shape of
  inequality (5)).
- `eventually_span_eq_top_of_linearIndependent`: for `[Finite ι]`, `[FiniteDimensional 𝕜 E]`,
  `f` with `hf : LinearIndependent 𝕜 f` and `hspan : Submodule.span 𝕜 (Set.range f) = ⊤`: for all
  `g` near `f`, `Submodule.span 𝕜 (Set.range g) = ⊤` (a basis at `ω₀` stays a basis nearby).
- `exists_local_decay_of_basis` (**local form of (4)**): for a normed space `F` over `𝕜`,
  `[FiniteDimensional 𝕜 E]`, a topological space `X`, `b : X → ι → E` and `ω₀ : X` with
  `hb : ContinuousAt b ω₀`, `hli : LinearIndependent 𝕜 (b ω₀)`,
  `hspan : Submodule.span 𝕜 (Set.range (b ω₀)) = ⊤`, maps `ℓ : ℕ → X → E →ₗ[𝕜] F`,
  `ψ : ℕ → X → E`, `t s h : ℕ → ℝ`, `V` with `hV : V ∈ 𝓝 ω₀`, reals `ε C₂ C₄`, `d : ℕ`,
  `hC₂ : 0 ≤ C₂`,
  `h₂ : ∀ ω ∈ V, ∀ n i, ‖ℓ n ω (b ω i)‖ ≤ C₂ * Real.exp (-(ε * h n))` and
  `h₄ : ∀ ω ∈ V, ∀ n j, ‖inner 𝕜 (b ω j) (ψ n ω)‖ ≤ C₄ * t n * (1 + s n) ^ d`: there are
  `U ∈ 𝓝 ω₀` and `C` with
  `‖ℓ n ω (ψ n ω)‖ ≤ C * t n * (1 + s n) ^ d * Real.exp (-(ε * h n))` for all `ω ∈ U` and all
  `n`.

### Uniformity on a compact set

- `IsDecayBoundedOn F t s h S` (definition), for `F : ℕ → X → ℝ`, `t s h : ℕ → ℝ` and
  `S : Set X` (any type `X`): there are `ε > 0`, `C : ℝ` and `d : ℕ` with
  `F n ω ≤ C * t n * (1 + s n) ^ d * Real.exp (-(ε * h n))` for all `ω ∈ S` and all `n` (the form
  of the bound (4)).
- `IsDecayBoundedOn.mono`: `IsDecayBoundedOn F t s h T → S ⊆ T → IsDecayBoundedOn F t s h S`.
- `isDecayBoundedOn_of_isCompact`: for a topological space `X`, `hS : IsCompact S`, `F`, `t`,
  `s`, `h` with `ht : ∀ n, 0 ≤ t n`, `hs : ∀ n, 0 ≤ s n`, `hh : ∀ n, 0 ≤ h n` and
  `hloc : ∀ ω₀ ∈ S, ∃ U ∈ 𝓝 ω₀, IsDecayBoundedOn F t s h U`: `IsDecayBoundedOn F t s h S`
  ("comme `𝒪` est compact, il suffit de prouver […] dans un voisinage convenable de `ω₀`").

### The limit

- `tendsto_one_add_mul_pow_mul_exp_neg A d hc`: for `A : ℝ`, `d : ℕ` and `c > 0`,
  `(1 + |A| * n) ^ d * Real.exp (-(c * n)) → 0` as `n → ∞` (`n : ℕ`).
- `tendsto_inv_smul_integral_of_decay`: for a measure `μ` on a measurable space `X`,
  `w : X → ℂ` with `hw : Integrable w μ`, `F : ℕ → X → ℂ`, `t s h : ℕ → ℝ` with
  `ht : ∀ n, 0 < t n` and `hs0 : ∀ n, 0 ≤ s n`, reals `A B ε C`, `d : ℕ`, `hB : 0 < B`,
  `hε : 0 < ε`, `hs : ∀ n, s n ≤ A * n`, `hh : ∀ n, B * n ≤ h n` and
  `hF : ∀ n, ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ C * t n * (1 + s n) ^ d * Real.exp (-(ε * h n))`:
  `(t n)⁻¹ • ∫ ω, w ω * F n ω ∂μ → 0`.
- `tendsto_inv_smul_integral_of_local_basis` (**(4) and `X⁺ = 0`**): for a finite-dimensional
  complex inner product space `E`, a compact topological space `X` with a measurable structure
  and a measure `μ`, `w` with `hw : Integrable w μ`, `ℓ : ℕ → X → E →ₗ[ℂ] ℂ`, `ψ : ℕ → X → E`,
  `t s h` with `ht : ∀ n, 0 < t n`, `hs0 : ∀ n, 0 ≤ s n`, reals `A B` with `hB : 0 < B`,
  `hs : ∀ n, s n ≤ A * n`, `hh : ∀ n, B * n ≤ h n`, and `hloc`: for every `ω₀` there are
  `k : ℕ` and `b : X → Fin k → E` with `ContinuousAt b ω₀`, `LinearIndependent ℂ (b ω₀)`,
  `Submodule.span ℂ (Set.range (b ω₀)) = ⊤`, and `V ∈ 𝓝 ω₀`, `ε > 0`, `C₂ ≥ 0`, `C₄`, `d` with
  `∀ ω ∈ V, ∀ n i, ‖ℓ n ω (b ω i)‖ ≤ C₂ * Real.exp (-(ε * h n))` and
  `∀ ω ∈ V, ∀ n j, ‖inner ℂ (b ω j) (ψ n ω)‖ ≤ C₄ * t n * (1 + s n) ^ d`. Conclusion:
  `(t n)⁻¹ • ∫ ω, w ω * ℓ n ω (ψ n ω) ∂μ → 0`.

## Proof

`exists_norm_le_norm_sum_smul_of_linearIndependent`: the map `c ↦ ∑ i, c i • f i` is injective
on the finite-dimensional space `ι → 𝕜`, hence antilipschitz with some constant `K > 0`
(`LinearMap.exists_antilipschitzWith`), so `‖c‖ ≤ K ‖∑ c_i f_i‖`. If
`S = ∑ i, ‖g i − f i‖ < (2K)⁻¹` (true near `f`), then
`‖∑ c_i f_i‖ ≤ ‖∑ c_i g_i‖ + ‖c‖ S`, so `‖c‖ ≤ K ‖∑ c_i g_i‖ + ‖c‖/2`, and `C = 2K`.

`exists_sum_norm_le_sum_norm_inner_of_linearIndependent`: with `w = ∑ c_i g_i` and
`S = ∑_j ‖⟪g_j, w⟫‖`, `‖w‖² = re ⟪w, w⟫ ≤ ‖∑_i c_i ⟪w, g_i⟫‖ ≤ ‖c‖ S ≤ C ‖w‖ S`, so
`‖w‖ ≤ C S`; then `∑ ‖c_i‖ ≤ card(ι) ‖c‖ ≤ card(ι) C ‖w‖ ≤ card(ι) C² S`.

`exists_norm_apply_le_of_linearIndependent`: write `w = ∑ c_i g_i`
(`Submodule.mem_span_range_iff_exists_fun`); `‖ℓ w‖ ≤ ∑ ‖c_i‖ ‖ℓ g_i‖ ≤ B ∑ ‖c_i‖` and the
previous result. For empty `ι`, `w = 0`; otherwise `B ≥ 0`.

`eventually_span_eq_top_of_linearIndependent`: `card ι = finrank E` (`finrank_span_eq_card`);
near `f` the family stays linearly independent (`LinearIndependent.eventually`), hence spans
(`LinearIndependent.span_eq_top_of_card_eq_finrank'`).

`exists_local_decay_of_basis`: by continuity of `b` at `ω₀`, the two previous properties hold
for `b ω` on a neighbourhood of `ω₀`, which is intersected with `V`. There
`ψ n ω ∈ span (b ω)`, and the bound with `B = C₂ e^{−ε h(n)}` gives
`‖ℓ n ω (ψ n ω)‖ ≤ C C₂ e^{−ε h(n)} · card(ι) C₄ t(n)(1 + s(n))^d`.

`isDecayBoundedOn_of_isCompact`: `IsCompact.induction_on` for the property "bounded with some
`ε > 0`, `C ≥ 0`, `d`" (which holds on `∅`, passes to subsets, and to unions with
`min ε₁ ε₂`, `max C₁ C₂`, `max d₁ d₂`, since `(1 + s)^{d₁} ≤ (1 + s)^d` for `s ≥ 0` and
`e^{−ε₁ h} ≤ e^{−ε h}` for `ε ≤ ε₁`, `h ≥ 0`); the local hypothesis gives it near every point
with `max C 0`.

`tendsto_one_add_mul_pow_mul_exp_neg`: `(1 + |A| n)^d ≤ (1 + |A|)^d (1 + n)^d`, and
`(1 + n)^d e^{−cn} = e^c c^{−d} x^d e^{−x}` with `x = c(1 + n) → ∞`
(`Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`).

`tendsto_inv_smul_integral_of_decay`: `‖∫ w F_n‖ ≤ (∫ ‖w‖) K_n` with
`K_n = C t(n)(1 + s(n))^d e^{−ε h(n)} ≤ |C| t(n) (1 + |A| n)^d e^{−εBn}`
(`norm_integral_le_of_norm_le`), so `‖t(n)⁻¹ ∫ w F_n‖ ≤ |C| (∫ ‖w‖) (1 + |A| n)^d e^{−εBn}`,
which tends to `0` by the previous result; conclude by `squeeze_zero_norm`.

`tendsto_inv_smul_integral_of_local_basis`: `h(n) ≥ Bn ≥ 0`; `exists_local_decay_of_basis` at
each `ω₀` gives `hloc` of `isDecayBoundedOn_of_isCompact` for `‖ℓ n ω (ψ n ω)‖` on
`Set.univ`, and `tendsto_inv_smul_integral_of_decay` applies to the uniform bound.
