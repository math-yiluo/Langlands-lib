# Translations on the Harish-Chandra Schwartz space

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.Translations`,
namespace `Langlands.HarishChandraSchwartz`. It builds on
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic`, which defines the levels `C_K`
(`Level Ξ σ K`) and their inductive limit `C(G)` (`Space Ξ σ`) for arbitrary weights `Ξ`
and `σ`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333.

- Section III.6 (printed p. 271, PDF p. 37): "Pour `f ∈ C(G)` et `g₁, g₂ ∈ G`, la fonction
  `ρ(g₁)λ(g₂)f` appartient à `C(G)` (cf. I.6 et Lemme II.1.2). L'application
  `G × G × C(G) → C(G)`, `(g₁, g₂, f) ↦ ρ(g₁)λ(g₂)f` est continue." Waldspurger gives
  no proof of the continuity.
- Section I.6 (printed p. 249, PDF p. 15): `ρ` and `λ` are the representations of `G` on
  smooth functions by right and left translation. The proof of Lemma I.6.1 on the same page
  identifies `λ(g₂⁻¹)ρ(g₁)f` with `g ↦ f(g₂ g g₁)`. So `ρ(g₁)λ(g₂)f` is the function
  `x ↦ f(g₂⁻¹ x g₁)`.
- Lemma II.1.2 (printed p. 251, PDF p. 17): there is `d ∈ ℕ` such that for all
  `g₁, g₂ ∈ G` there is `C > 0` with `Ξ(g₁ g g₂) ≤ C Ξ(g) (1 + σ(g))^d` for all `g ∈ G`.

## Scope: generic weights and explicit hypotheses

The weights `Ξ σ : G → ℝ` are arbitrary. The results on translations assume the structure
`TranslationWeights Ξ σ`, whose fields are:

- `pos`: `Ξ g > 0` for all `g`;
- `nonneg`: `σ g ≥ 0` for all `g`;
- `bound : TranslationBound Ξ σ`, the statement of Lemma II.1.2 for `Ξ` and `σ`. The
  constant `C` is not required to be positive. When `Ξ > 0` this makes no difference,
  because the inequality at `g = 1` forces `C > 0`.
- `heightBound : HeightTranslationBound σ`: for all `g₁, g₂` there is `C` with
  `1 + σ(g₁ g g₂) ≤ C (1 + σ(g))` for all `g`.

Waldspurger does not state `HeightTranslationBound` as a separate result. It follows from
the inequality `1 + σ(g) ≤ (1 + σ(h))(1 + σ(h⁻¹g))` that he uses in the proof of
Lemma III.6.1 (printed p. 272, PDF p. 38). This module proves the implication as
`heightTranslationBound_of_le_add`: a nonnegative subadditive `σ` satisfies the bound, with
`C = (1 + σ(g₁))(1 + σ(g₂))`. The height `σ = log ‖·‖` of
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.Height` is nonnegative (`height_nonneg`)
and subadditive (`height_mul_le`).

This module does not prove Lemma II.1.2 for Waldspurger's `Ξ`. That lemma uses the Cartan
decomposition and the asymptotics of the matrix coefficients of `I_{P₀}^G 1`, and it remains
an explicit hypothesis here.

The group `G` is a topological group. The results that use the inductive limit topology
also assume that `G` has a compact open subgroup (`Nonempty (CompactOpenSubgroup G)`), as
`Basic` does.

## Definitions

- `translate g₁ g₂ f`: the function `x ↦ f(g₂⁻¹ x g₁)`, that is, `ρ(g₁)λ(g₂)f`, on
  arbitrary functions `G → ℂ`.
- `conjSubgroup g H`: the conjugate subgroup `g H g⁻¹ = {x | g⁻¹ x g ∈ H}`.
- `CompactOpenSubgroup.conj g K` and `CompactOpenSubgroup.translate g₁ g₂ K`: the compact
  open subgroups `g K g⁻¹` and `g₁ K g₁⁻¹ ∩ g₂ K g₂⁻¹`.
- `TranslationBound Ξ σ`, `HeightTranslationBound σ`, `TranslationWeights Ξ σ`: the
  hypotheses described above. All three are `Prop`-valued.
- `Level.translate hw g₁ g₂ K`: `ρ(g₁)λ(g₂)` as a linear map
  `C_K → C_{g₁ K g₁⁻¹ ∩ g₂ K g₂⁻¹}`.
- `Space.translateLinear hw g₁ g₂` and `Space.translate hw g₁ g₂`: `ρ(g₁)λ(g₂)` as a linear
  map and as a continuous linear map `C(G) → C(G)`.

## Results

- `translate_one_one`, `translate_translate`: `ρ(1)λ(1) = id` and
  `ρ(g₁)λ(g₂) ρ(h₁)λ(h₂) = ρ(g₁h₁)λ(g₂h₂)`. The same identities on `C(G)` are
  `Space.translate_one_one` and `Space.translate_translate`.
- `IsBiInvariant.translate_eq`: an `H`-bi-invariant function is fixed by `ρ(h₁)λ(h₂)` for
  `h₁, h₂ ∈ H`.
- `IsBiInvariant.translate`: if `f` is `H`-bi-invariant, then `ρ(g₁)λ(g₂)f` is bi-invariant
  under `g₁ H g₁⁻¹ ∩ g₂ H g₂⁻¹`.
- `HeightTranslationBound.exists_rpow_le`: for fixed `g₁, g₂` there is `M ≥ 1` with
  `(1 + σ(g₁ y g₂))^s ≤ M^{|s|} (1 + σ(y))^s` for all real `s` and all `y`.
- `TranslationWeights.nu_translate_le`: for fixed `g₁, g₂` there is `d ∈ ℕ` such that for
  every `r` there is `c ≥ 0` with `ν_r(ρ(g₁)λ(g₂)f) ≤ c ν_{r+d}(f)` for all `f : G → ℂ`.
  With `y = g₂⁻¹ x g₁`, Lemma II.1.2 gives `Ξ(x)⁻¹ ≤ C (1 + σ(x))^d Ξ(y)⁻¹`, and
  `exists_rpow_le` compares `(1 + σ(x))^{r+d}` with `(1 + σ(y))^{r+d}`.
- `TranslationWeights.translate_mem_levelSubmodule` and
  `TranslationWeights.translate_mem_schwartzSubmodule`: `ρ(g₁)λ(g₂)` maps `C_K` into
  `C_{g₁ K g₁⁻¹ ∩ g₂ K g₂⁻¹}`, and hence `C(G)` into itself. This is the first assertion
  of III.6 quoted above.
- `Level.continuous_translate`: `ρ(g₁)λ(g₂) : C_K → C_{g₁ K g₁⁻¹ ∩ g₂ K g₂⁻¹}` is continuous,
  by the seminorm estimate `nu_translate_le`.
- `Space.translate`: the continuity of `ρ(g₁)λ(g₂)` on `C(G)` follows from the continuity on
  each level, by property III.6(1) of the inductive limit (`mkCLM` in `Basic`).
- `Space.nhds_zero_of_forall_level`: an equicontinuity criterion for `C(G)`. Let
  `(T_i)_{i ∈ ι}` be a family of linear maps from `C(G)` to a locally convex space `V`. If
  for every level `C_K` and every neighbourhood `W` of `0` in `V` the set
  `{f ∈ C_K | T_i f ∈ W for all i}` is a neighbourhood of `0` in `C_K`, then
  `{f ∈ C(G) | T_i f ∈ W for all i}` is a neighbourhood of `0` in `C(G)`.
- `Space.translate_nhds_zero`: for a compact open subgroup `H`, the family
  `(ρ(k₁)λ(k₂))_{k₁, k₂ ∈ H}` is equicontinuous at `0` on `C(G)`.
- `Space.continuous_translate`: the map `G × G × C(G) → C(G)`,
  `((g₁, g₂), f) ↦ ρ(g₁)λ(g₂)f`, is continuous. This is the continuity assertion of III.6.

## Proofs

**Equicontinuity criterion.** Equip `C(G)` with the topology `t` of uniform convergence of
the family `T`: the topology induced by `f ↦ (T_i f)_i` into the space `ι →ᵤ V` of functions
with the uniform structure of uniform convergence. This is an additive group topology. It is
locally convex, because the sets `{f | T_i f ∈ S for all i}` with `S` a convex
neighbourhood of `0` form a basis at `0`. Scalar multiplication is continuous, because for
each `f` the set `{T_i f | i ∈ ι}` is bounded in `V`. This boundedness follows from the
hypothesis: `f` lies in some level `C_K`, and neighbourhoods of `0` in `C_K` absorb `f`.
By the hypothesis, every inclusion `C_K → (C(G), t)` is continuous at `0` and hence
continuous. The topology of `C(G)` is the finest locally convex vector topology for which
these inclusions are continuous (`topologicalSpace_le_iff` in `Basic`), so it is finer than
`t`. A neighbourhood `W` of `0` in `V` contains a convex neighbourhood `S`, and
`{f | T_i f ∈ S for all i}` is a neighbourhood of `0` for `t`, hence for the topology of
`C(G)`.

**Equicontinuity of `H`-translations.** Apply the criterion to `T_k = ρ(k₁)λ(k₂)` for
`k = (k₁, k₂) ∈ H × H`. Fix a level `C_K`. The map `k ↦ ρ(k₁)λ(k₂) ∘ (C_K → C(G))` is
locally constant on `H × H`. For `f ∈ C_K` the value of `ρ(k₁)λ(k₂)f` depends only on the
cosets `k₁K` and `k₂K`, because `f` is `K`-bi-invariant. Since `H × H` is compact, the map
takes only finitely many values. So the set in the criterion is a finite intersection of
preimages of `W` under continuous linear maps, and it is a neighbourhood of `0` in `C_K`.

**Joint continuity.** Fix `(g₁, g₂, f₀)`. Then `f₀` lies in some level `C_H`. Let
`A = ρ(g₁)λ(g₂)`. For `x₁ ∈ g₁H`, `x₂ ∈ g₂H` and `f ∈ C(G)`, put `k₁ = g₁⁻¹x₁` and
`k₂ = g₂⁻¹x₂`. Since `f₀` is `H`-bi-invariant, `ρ(k₁)λ(k₂)f₀ = f₀`, and therefore

`ρ(x₁)λ(x₂)f = A(ρ(k₁)λ(k₂)(f - f₀)) + A f₀`.

Let `W` be a neighbourhood of `A f₀`. By the continuity of `A`, the set
`W' = {u | A u + A f₀ ∈ W}` is a neighbourhood of `0`. By the equicontinuity of the
`H`-translations, the set `U = {u | ρ(k₁)λ(k₂)u ∈ W' for all k₁, k₂ ∈ H}` is a
neighbourhood of `0`. Then the neighbourhood `g₁H × g₂H × (f₀ + U)` of `(g₁, g₂, f₀)` is
mapped into `W`.

The source states the continuity without proof. This argument is the standard one for
inductive limits of this kind, and the Lean proof implements it.

## Not covered here

Lemma III.6.1 (convolution), the constant term `f^{(P)}` of III.6, and the instantiation of
`Ξ` and `σ` by Waldspurger's spherical function and height are left to other modules.
