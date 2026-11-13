# Characters under conjugation and duality for non-unimodular groups (Renard III.1.12): statements

Module `Langlands.Representation.Character.ModularTransportStatement`. Namespace `Langlands`.
Universe parameters `uG` (the group) and `uV` (the representation space).
The module contains two **statements**, the `Prop`-valued definitions
`CharacterConjugationModularStatement` and `CharacterContragredientModularStatement`. It
proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The published, proved `CharacterTransportStatement`
([TransportStatement](TransportStatement.md)) treats automorphisms that preserve the chosen
measure and the contragredient for a measure invariant under inversion. For an inner
automorphism, the first condition holds when `G` is unimodular. The second condition says that
the left Haar measure is also right invariant. So for a non-unimodular `G` neither published
statement gives the III.1.12 Lemma or Example, which carry the modular factors `δ_G(g₀)` and
`δ_G⁻¹`. This unit states them for every t.d. group.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read III.1.12, printed p.65 / PDF p.71:

> Si l'on fixe une mesure de Haar à gauche `μ_G`, pour tout `f ∈ 𝒟(G)`, on pose
> `Θ_π(f) = Tr π(f) := Tr π(f μ_G)`. […]
>
> Lemme. Soit `g₀ ∈ G` et `Int(g₀)` l'automorphisme intérieur de `G` donné par la conjugaison
> par `g₀`. On a alors, pour toute représentation admissible `(π, V)` de `G` :
> `Int(g₀) · (Tr π) = δ_G(g₀) Tr π`. En particulier si `G` est unimodulaire, `Tr π` est une
> distribution invariante par conjugaison.
>
> Démonstration. […] `(Int(g₀) · Tr π)(f) = Tr π(Int(g₀⁻¹)(f)) = Tr π(Int(g₀⁻¹)(f) μ_G)
> = δ_G(g₀) Tr π(Int(g₀⁻¹) · (f μ_G)) = δ_G(g₀) Tr π(f μ_G) = δ_G(g₀) Tr π(f)`.
>
> Exemple. Soit `(π, V)` une représentation admissible de `G`. Le caractère de la
> représentation contragrédiente `(π̃, Ṽ)` est donné par `Θ_π̃(T) = Θ_π(Ť)`, `(T ∈ H(G))`,
> `Θ_π̃(f) = Θ_π(f̌ δ_G⁻¹)`, `(f ∈ 𝒟(G))`. On rappelle que `f̌` est définie par
> `f̌(g) = f(g⁻¹)`.

In the proof, `Int(g₀⁻¹)` acts on distributions by `T ↦ δ_{g₀⁻¹} ∗ T ∗ δ_{g₀}`, the
pushforward along `x ↦ g₀⁻¹ x g₀`. On functions it is the corresponding transport
`f ↦ (x ↦ f(g₀ x g₀⁻¹))`. So the Lemma reads `Θ_π(x ↦ f(g₀ x g₀⁻¹)) = δ_G(g₀) Θ_π(f)`.

## Published objects used

- `Character.distribution μ ρ hρ`, the character `Θ_ρ(f) = Tr ρ(f μ)` of an admissible
  representation for a left invariant measure `μ` ([Basic](Basic.md)).
- `HarmonicAnalysis.Distribution.renardModular : G →* ℝ≥0`, Renard's modular character
  `δ_G` (`r(g) μ = δ_G(g) μ`), the inverse of Mathlib's modular character
  ([Distribution/Haar](../../HarmonicAnalysis/Distribution/Haar.md)).
- `smoothContragredient`, `IsAdmissible`, `SchwartzBruhat` (the test functions `𝒟(G)`).

## The statements

Let `G` be a t.d. group (Hausdorff, locally compact, totally disconnected) with its Borel
structure, `μ` a left Haar measure, and `ρ` an admissible complex representation.

**`CharacterConjugationModularStatement`** (Lemma). For `g₀ ∈ G` and `f ∈ 𝒟(G)` there is a
test function `h` with `h(x) = f(g₀ x g₀⁻¹)` for all `x`, and `Θ_ρ(h) = δ_G(g₀) Θ_ρ(f)`.

**`CharacterContragredientModularStatement`** (Example). The smooth contragredient `ρ̃` is
admissible, and for every `f ∈ 𝒟(G)` there is a test function `h` with
`h(g) = f(g⁻¹) δ_G(g)⁻¹` for all `g`, and `Θ_ρ̃(f) = Θ_ρ(h)`.

## Formalization choices

- **Test functions defined by a formula.** The transformed test functions are asserted to
  exist with the given values, rather than constructed in the statement. The values determine
  them. This is Renard's "on vérifie" that they are test functions.
- **The Hecke-algebra form `Θ_π̃(T) = Θ_π(Ť)`** of the Example is not restated. In the
  published Hecke algebra `Ť` is the weighted inversion `haarInversion`,
  `f ↦ (g ↦ Δ(g) f(g⁻¹))` with `Δ = δ_G⁻¹`. So that form is the test-function identity
  above.
- **"En particulier si `G` est unimodulaire …"** is the published
  `Character.distribution_isConjugationInvariant_of_measurePreserving` and
  `CharacterAutomorphismStatement`. It is also the case `δ_G = 1` of the first statement.
- **Admissibility of `ρ̃`** is part of the Example's statement, so that its character is
  defined. It is the published `SmoothAdmissibleDualityStatement`, since compact open
  subgroups are cofinal in a t.d. group.

## Why the statements are true

Write `Δ` for Mathlib's modular character, so `map (· * g) μ = Δ(g) μ` and `δ_G = Δ⁻¹`.

1. **Lemma.** The map `c(x) = g₀ x g₀⁻¹` is right multiplication by `g₀⁻¹` followed by left
   multiplication by `g₀`, so `c_* μ = Δ(g₀⁻¹) μ = δ_G(g₀) μ`. Write the integrand of
   `ρ(f ∘ c) = ∫ f(c x) ρ(x) dμ(x)` as `F(c x)` with `F(y) = f(y) ρ(g₀⁻¹ y g₀)`. Then
   `ρ(f ∘ c) = ∫ F d(c_* μ) = δ_G(g₀) ∫ f(y) ρ(g₀⁻¹ y g₀) dμ(y) = δ_G(g₀) ρ(g₀)⁻¹ ρ(f) ρ(g₀)`.
   Taking traces of these finite-rank operators gives `Θ_ρ(f ∘ c) = δ_G(g₀) Θ_ρ(f)`.
2. **Example.** Let `h(g) = f(g⁻¹) δ_G(g)⁻¹`. It is locally constant with compact support,
   because `δ_G` is locally constant. The argument works with the integrated operators, as
   Renard's does; the pointwise operators `ρ(g)` need not preserve `V^K`.
   - *Duality of integrated operators.* For `ℓ ∈ Ṽ` and `v ∈ V`,
     `⟨ρ̃(f) ℓ, v⟩ = ∫ f(g) ℓ(ρ(g⁻¹) v) dμ(g) = ℓ(ρ(h) v)`. The second equality is the inversion
     formula for a left Haar measure, `∫ F(g⁻¹) dμ(g) = ∫ F(g) δ_G(g)⁻¹ dμ(g)`, applied to the
     scalar function `F(y) = f(y⁻¹) ℓ(ρ(y) v)`. This is the III.1.6 pairing identity
     `(π̃(Ť) · λ)(v) = λ(π(T) · v)` for the Haar density, Ť being the weighted inversion.
   - *Finite-dimensional reduction.* Choose a compact open `K` such that `f` is bi-invariant
     under `K`, that is `f = e_K ∗ f ∗ e_K` as in III.1.12. Then `h` is also bi-invariant under
     `K`, since `δ_G` is trivial on `K`. So `ρ(h)` maps `V` into `V^K` and vanishes on the kernel
     of `ρ(e_K)`, and `ρ̃(f)` maps `Ṽ` into `Ṽ^K` and vanishes on the kernel of `ρ̃(e_K)`. The
     characters are the traces of the restrictions `ρ(h)|_{V^K}` and `ρ̃(f)|_{Ṽ^K}`, which act on
     finite-dimensional spaces by admissibility.
   - *Transpose.* Restriction of functionals identifies `Ṽ^K` with `(V^K)^*` (III.1.6; the
     published `SmoothDualCompactFixedDualityStatement`). By the duality identity, `ρ̃(f)|_{Ṽ^K}`
     is the transpose of `ρ(h)|_{V^K}` under this identification. A linear map and its transpose
     have the same trace, so `Θ_ρ̃(f) = Θ_ρ(h)`.

## Remaining obligations

The proofs are a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Character.TransportStatement` | `Character.distribution`, `smoothContragredient`, `SchwartzBruhat`, `IsAdmissible` (through its imports) |
| `Langlands.HarmonicAnalysis.Distribution.Haar` | `Distribution.renardModular` |
