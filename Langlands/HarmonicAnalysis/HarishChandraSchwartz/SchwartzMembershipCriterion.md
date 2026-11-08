# A membership criterion for `C_H` (the structure of the proof of Proposition VI.3.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzMembershipCriterion`,
namespace `Langlands.HarishChandraSchwartz`. It imports
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientCutoff` and uses from it and its
imports `nu`, `weight`, `levelSubmodule` and `IsBiInvariant` (`Basic`); from Mathlib
`Finset.single_le_sum`, `Real.rpow_le_rpow_of_nonpos`, `Real.rpow_le_rpow_of_exponent_le`,
`Real.rpow_add`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`), proof of Proposition VI.3.1. Printed page numbers;
the PDF page is the printed page minus 234. The quotes from pages 302–303 were checked on the
rendered PDF pages 68 and 69.

- Printed p. 302 (PDF p. 68): "Il s'agit de prouver que `f_{ϕ,ψ} ∈ 𝒞_H` (cf. III.6) […] Pour
  `m ∈ M`, posons `s(m) = sup{|⟨α, H_0(m)⟩|; α ∈ Δ_0}`. Pour tout sous-ensemble `J ⊂ Δ_0`,
  posons `M̄_0^+(J) = {m ∈ M̄_0^+; {α ∈ Δ_0; ⟨α, H_0(m)⟩ = s(m)} = J}` […] Pour `f ∈ C_lisse(G)`,
  `r ∈ ℝ`, `J ⊂ Δ_0`, posons `ν_{r,J}(f) = sup{|f(m)|Ξ(m)^{−1}(1 + σ(m))^r; m ∈ M̄_0^+(J)}`. En
  vertu de I.1 (4) et de l'égalité `M̄_0^+ = ⋃_{J⊂Δ_0} M̄_0^+(J)`, il existe un ensemble fini
  `𝓕 ⊂ L(ω_B, P)` tel que pour tout `ϕ` et tout `r`, `ν_r(f_{ϕ,ψ}) = sup{ν_{r,J}(f_{ϕ,ψ'});
  ψ' ∈ 𝓕, J ⊂ Δ_0}`."
- Printed p. 303 (PDF p. 69): the bounds `n(ϕ)` on `{m ∈ M̄_0^+(J); s(m) ⩽ t}`, `n^w(ϕ)` and
  `n^+(ϕ)` for the weak and positive parts, "Alors `ν_{r,J}(f_{ϕ,ψ}) ⩽ n(ϕ) + n^w(ϕ) + n^+(ϕ)`",
  and the bound `|f_{ϕ,ψ}(g)| ⩽ (1 + |H_G(g)|)^{−r} Ξ(g) ν^M(D, ϕ)`.
- Printed p. 304 (PDF p. 70): "Remarquons qu'il existe `C > 0` tel que si `m ∈ M_0` vérifie
  `s(m) ⩽ t`, alors `1 + σ(m) ⩽ C(1 + |H_G(m)|)`. On en déduit l'assertion (2) pour le terme
  `n(ϕ)`".
- III.6, printed p. 271: `ν_r(f) = sup{|f(g)|Ξ(g)^{−1}(1 + σ(g))^r; g ∈ G}` and `𝒞_H` is the space
  of `f ∈ C(H \ G / H)` with `ν_r(f)` finite for every `r`.

The abstraction, the hypotheses and the proof route are internal to this project.

## Relation to the source

- `IsRapidlyDecreasingOnSet Ξ σ S f` states that `sup{|f(m)|Ξ(m)^{−1}(1 + σ(m))^r; m ∈ S}` is
  finite for every `r` (in the form `|f| ≤ c_r Ξ (1 + σ)^{−r}`), i.e. the finiteness of `ν_{r,J}`
  for `S = M̄_0^+(J)`, of `n(ϕ)` for `S = M̄_0^+(J) ∩ {s ≤ t}`, and of `n^w`, `n^+`.
- `isRapidlyDecreasingOnSet_univ_of_cartan` is the reduction "En vertu de I.1 (4)": `G = K S K`
  (I.1 (4)) with `S` playing `M̄_0^+`, `Ξ` and `σ` bi-invariant under `K` (Lemmas II.1.1 and the
  definition of `σ`), and the finitely many functions `x ↦ f(k₁ x k₂)`, `k₁, k₂ ∈ K`, in a finite
  set `Ff` (the source's `𝓕`, finite since `f` is bi-invariant under an open subgroup and `K` is
  compact; this finiteness is a hypothesis). Covering `S` by the pieces `M̄_0^+(J)` and the pieces
  by `{s ≤ t}` and `{s ≥ t}` is done with `isRapidlyDecreasingOnSet_biUnion` and
  `IsRapidlyDecreasingOnSet.union`.
- `isRapidlyDecreasingOnSet_of_le_rpow` is the step for `n(ϕ)`, with `L` in place of
  `|H_G|` and the inequality `1 + σ ≤ C (1 + L)` on the region as a hypothesis; the bound in
  `1 + L` itself is the form of `exists_norm_inducedOrbitWavePacket_le_xi_rpow`
  (`OrbitWavePacketDecay`, with `L = ‖n_G‖`).
- `IsRapidlyDecreasingOnSet.add` combines the weak and positive parts on `{s ≥ t}`; the factor
  `δ_{P'}(m)^{1/2}`, the bounds `n^w` (by induction on the semisimple rank, Proposition V.1.1)
  and `n^+` (Lemma VI.2.3) are not part of this module.
- The continuity of `ψ ↦ f_ψ` (the bound by `ν^M(D, ϕ)`) is not formalized here.

## Contents

Section `Rapid` (a type `G`, `Ξ σ : G → ℝ`):

- `IsRapidlyDecreasingOnSet Ξ σ S f` (definition), for `S : Set G` and `f : G → ℂ`: for every
  `r : ℝ` there is `c` with `‖f x‖ ≤ c * Ξ x * (1 + σ x) ^ (-r)` for all `x ∈ S`.
- `IsRapidlyDecreasingOnSet.mono`: restriction to a subset `T ⊆ S`.
- `IsRapidlyDecreasingOnSet.exists_nonneg`: for `hΞ0 : ∀ g, 0 ≤ Ξ g` and
  `hσ0 : ∀ g, 0 ≤ σ g`, the constant may be taken `≥ 0`.
- `IsRapidlyDecreasingOnSet.union`: for `hΞ0`, `hσ0`, rapid decay on `S` and on `T` gives rapid
  decay on `S ∪ T`.
- `isRapidlyDecreasingOnSet_biUnion`: for `hΞ0`, `hσ0`, a finite set `s` of indices,
  `T : ι → Set G` and rapid decay on every `T i`, `i ∈ s`: rapid decay on `⋃ i ∈ s, T i`.
- `IsRapidlyDecreasingOnSet.add`: for `hΞ0`, `hσ0`, rapid decay of `f₁` and `f₂` on `S` gives
  rapid decay of `f₁ + f₂`.
- `isRapidlyDecreasingOnSet_of_le_rpow`: for `hΞ0`, `hσ0`, `L : G → ℝ` with
  `hL0 : ∀ x ∈ S, 0 ≤ L x`, `hL : ∃ C, ∀ x ∈ S, 1 + σ x ≤ C * (1 + L x)` and
  `hb : ∀ r, ∃ c, ∀ x ∈ S, ‖f x‖ ≤ c * Ξ x * (1 + L x) ^ (-r)`: rapid decay on `S`.
- `nu_lt_top_of_isRapidlyDecreasingOnSet_univ`: for `hΞ : ∀ g, 0 < Ξ g`, `hσ0` and rapid decay
  on `Set.univ`: `nu Ξ σ r f < ⊤` for every `r`.

Section `Cartan` (moreover `[Group G]`):

- `isRapidlyDecreasingOnSet_univ_of_cartan`: for `hΞ0`, `hσ0`, a subgroup `K`, `S : Set G`,
  `hcartan : ∀ g, ∃ k₁ ∈ K, ∃ x ∈ S, ∃ k₂ ∈ K, g = k₁ * x * k₂`,
  `hΞK : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, Ξ (k₁ * g * k₂) = Ξ g`, `hσK` (the same for `σ`), `f`, a finite
  set `Ff` of functions with `hFf : ∀ k₁ ∈ K, ∀ k₂ ∈ K, (fun x => f (k₁ * x * k₂)) ∈ Ff` and
  `hS : ∀ φ ∈ Ff, IsRapidlyDecreasingOnSet Ξ σ S φ`: `IsRapidlyDecreasingOnSet Ξ σ Set.univ f`.
- `mem_levelSubmodule_of_cartan`: for `hΞ : ∀ g, 0 < Ξ g`, `hσ0`, subgroups `H` and `K`, `S`,
  `hcartan`, `hΞK`, `hσK`, `hf : IsBiInvariant H f`, `Ff`, `hFf` and `hS`:
  `f ∈ levelSubmodule Ξ σ H`.

## Proof

`IsRapidlyDecreasingOnSet.union`, `.add`, `isRapidlyDecreasingOnSet_biUnion`: add the
nonnegative constants (induction on the finite set for the union).

`isRapidlyDecreasingOnSet_of_le_rpow`: with `t = max r 0` and `C' = max C 1`,
`(1 + L)^{−t} ≤ ((1 + σ)/C')^{−t} = C'^t (1 + σ)^{−t} ≤ C'^t (1 + σ)^{−r}`.

`isRapidlyDecreasingOnSet_univ_of_cartan`: for `g = k₁ x k₂`, `f(g)` is the value at `x ∈ S` of
an element of `Ff`, and `Ξ(g) = Ξ(x)`, `σ(g) = σ(x)`; the constant is the sum of the nonnegative
constants of the elements of `Ff`.

`nu_lt_top_of_isRapidlyDecreasingOnSet_univ`: `|f(g)| Ξ(g)^{−1} (1 + σ(g))^r ≤ c_r` for every
`g`, so the supremum `ν_r(f)` is at most `c_r`. `mem_levelSubmodule_of_cartan`: the two previous
results and the definition of `levelSubmodule`.
