# Reduction of Corollary III.1.2 to exponential bounds on the positive chamber

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientRapidDecay`, namespace
`Langlands.HarishChandraSchwartz`. It imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientCutoff` and uses its predicate
`IsRapidlyDecreasingOn Ξ σ N f` (for every `r` there is `c` with
`‖f n‖ ≤ c * Ξ n * (1 + σ n) ^ (-r)` for `n ∈ N`), the conclusion of Corollary III.1.2 for one
coefficient; from Mathlib `Real.add_one_le_exp`, `Real.rpow_le_rpow_of_nonpos`,
`Real.rpow_le_rpow_of_exponent_le`, `Finset.single_le_sum`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`). Printed page numbers; the PDF page is the printed
page minus 234. The quotes were checked on the rendered PDF pages 29 and 30.

- Corollary III.1.2, printed p. 263 (PDF p. 29): "Supposons `π` de carré intégrable. Alors pour
  tout `f ∈ 𝒜(π)` et tout `r ∈ ℝ`, il existe `c > 0` tel que pour tout `g ∈ G¹`, on ait
  l'inégalité `|f(g)| ⩽ cΞ(g)(1 + σ(g))^{−r}`."
- Its proof, printed p. 264 (PDF p. 30): "On peut supposer `f` de la forme
  `f(g) = ⟨π(g)v, v̌⟩` pour des éléments `v ∈ V`, `v̌ ∈ V̌`. Grâce à I.1 (4) et à un argument de
  `K`-finitude, on peut se limiter à démontrer l'inégalité pour `g ∈ M̄_0^+ ∩ G¹`." Then, for the
  function (1), with `δ_P(a)^{1/2} ⩽ C₁Ξ(a)`, `|Q_χ(H_M(a))| ⩽ C₂(1 + σ(a))^d` and
  `|χ(a)| ⩽ C₃q^{−εσ(a)}`: "Pour tout `r ∈ ℝ`, il existe donc `c > 0` tel que la fonction (1)
  soit majorée par `cΞ(a)(1 + σ(a))^{−r}`."

The abstraction, the hypotheses and the proof route are internal to this project.

## Relation to the source

- `isRapidlyDecreasingOn_of_cartan` is the reduction "Grâce à I.1 (4) et à un argument de
  `K`-finitude": `N` plays `G¹`, `S` plays `M̄_0^+ ∩ G¹` and `K` the special maximal compact
  subgroup, with `N ⊆ K S K` (I.1 (4)) and `Ξ`, `σ` bi-invariant under `K` as hypotheses; the
  `K`-finiteness of `v` and of the functional `ℓ` (`v̌`) is the hypothesis that `ρ(K) v` and
  `ℓ ∘ ρ(K)` lie in finite sets `Vf`, `Lf` (for a smooth `v`, a smooth `ℓ` and compact `K` these
  orbits are finite; this is not proved here).
- `exists_rpow_bound_of_exp_bound` is the last step ("Pour tout `r` … il existe donc `c`"), in
  the following form: the chamber is covered by finitely many sets `T i` on each of which the
  coefficient is bounded by `C Ξ e^{−ε ‖H‖}` (`IsExpDecreasingOn`; in the source the bound
  `δ_P^{1/2} Σ χ Q_χ ⩽ C Ξ (1 + σ)^d q^{−εσ}` on `Ā_0^+ ∩ A_M ∩ G¹`, the polynomial factor being
  absorbed into the exponential), and `1 + σ ⩽ c (1 + ‖H‖)` on `S` (`H` playing `H_0`).
- The exponential bounds themselves (from Proposition III.1.1 via the exponents of the Jacquet
  modules, Proposition I.4.3 and Lemma II.1.1) are hypotheses here; Corollary III.1.2 for a
  square-integrable representation is not proved in this module.

## Contents

Section `Elementary`:

- `exists_exp_neg_le_rpow`: for `hε : 0 < ε` and `t : ℝ`, there is `K` with `0 ≤ K` and
  `Real.exp (-(ε * x)) ≤ K * (1 + x) ^ (-t)` for every `x ≥ 0`.
- `IsExpDecreasingOn Ξ H T F` (definition), for a type `X`, a seminormed group `E`,
  `Ξ : X → ℝ`, `H : X → E`, `T : Set X` and `F : X → ℂ`: there are `ε > 0` and `C` with
  `‖F x‖ ≤ C * Ξ x * Real.exp (-(ε * ‖H x‖))` for every `x ∈ T`.
- `exists_rpow_bound_of_exp_bound`: for `S : Set X`, `Ξ σ : X → ℝ`, `H : X → E`, `F : X → ℂ`,
  `hΞ0 : ∀ x ∈ S, 0 ≤ Ξ x`, `hσ0 : ∀ x ∈ S, 0 ≤ σ x`,
  `hσH : ∃ c, ∀ x ∈ S, 1 + σ x ≤ c * (1 + ‖H x‖)`, a finite set `s` of indices, `T : ι → Set X`
  with `hcover : S ⊆ ⋃ i ∈ s, T i` and `hexp : ∀ i ∈ s, IsExpDecreasingOn Ξ H (T i) F`: for every
  `r` there is `c` with `‖F x‖ ≤ c * Ξ x * (1 + σ x) ^ (-r)` for `x ∈ S`.

Section `Cartan` (a group `G`, a complex vector space `V`):

- `isRapidlyDecreasingOn_of_cartan`: for `ρ : Representation ℂ G V`, `Ξ σ : G → ℝ` with
  `hΞ0 : ∀ g, 0 ≤ Ξ g`, `hσ0 : ∀ g, 0 ≤ σ g`, subgroups `N K`, `S : Set G`,
  `hcartan : ∀ n ∈ N, ∃ k₁ ∈ K, ∃ x ∈ S, ∃ k₂ ∈ K, n = k₁ * x * k₂`,
  `hΞK`, `hσK` (`Ξ` and `σ` invariant under `g ↦ k₁ g k₂` for `k₁, k₂ ∈ K`), `v : V`,
  `ℓ : V →ₗ[ℂ] ℂ`, finite sets `Vf`, `Lf` with `hVf : ∀ k ∈ K, ρ k v ∈ Vf` and
  `hLf : ∀ k ∈ K, ℓ ∘ₗ ρ k ∈ Lf`, and
  `hS : ∀ v' ∈ Vf, ∀ ℓ' ∈ Lf, ∀ r, ∃ c, ∀ x ∈ S, ‖ℓ' (ρ x v')‖ ≤ c * Ξ x * (1 + σ x) ^ (-r)`:
  `IsRapidlyDecreasingOn Ξ σ N (fun g => ℓ (ρ g v))`.
- `isRapidlyDecreasingOn_of_cartan_of_exp`: the same data except `hS`, together with a
  seminormed group `E`, `H : G → E`, `hσH : ∃ c, ∀ x ∈ S, 1 + σ x ≤ c * (1 + ‖H x‖)`, a finite
  `s`, `T : ι → Set G` with `hcover : S ⊆ ⋃ i ∈ s, T i` and
  `hexp : ∀ v' ∈ Vf, ∀ ℓ' ∈ Lf, ∀ i ∈ s, IsExpDecreasingOn Ξ H (T i) (fun x => ℓ' (ρ x v'))`:
  `IsRapidlyDecreasingOn Ξ σ N (fun g => ℓ (ρ g v))`.

## Proof

`exists_exp_neg_le_rpow`: with `n = ⌈max t 0⌉` and `M = max 1 (n/ε)`, `1 + x ⩽ M (1 + εx/n)`
and `(1 + εx/n)^n ⩽ e^{εx}` (`Real.add_one_le_exp`), so `(1 + x)^n ⩽ M^n e^{εx}`, i.e.
`e^{−εx} ⩽ M^n (1 + x)^{−n} ⩽ M^n (1 + x)^{−t}`.

`exists_rpow_bound_of_exp_bound`: with `t = max r 0`, `c₁ = max c 1` and `K_i` from the previous
lemma for `ε_i`, a point `x ∈ S` lies in some `T i`, and
`‖F x‖ ⩽ |C_i| Ξ(x) K_i (1 + ‖H x‖)^{−t} ⩽ |C_i| K_i c₁^t Ξ(x) (1 + σ(x))^{−r}`, using
`(1 + σ)/c₁ ⩽ 1 + ‖H‖`; the constant is `Σ_{i ∈ s} |C_i| K_i c₁^t`.

`isRapidlyDecreasingOn_of_cartan`: write `n = k₁ x k₂`; then
`ℓ(ρ(n) v) = (ℓ ∘ ρ(k₁))(ρ(x)(ρ(k₂) v))` with `(ρ(k₂) v, ℓ ∘ ρ(k₁)) ∈ Vf × Lf`, and
`Ξ(n) = Ξ(x)`, `σ(n) = σ(x)`; the constant is the sum of `|c|` over `Vf × Lf`.

`isRapidlyDecreasingOn_of_cartan_of_exp`: the previous result, with `hS` given by
`exists_rpow_bound_of_exp_bound`.
