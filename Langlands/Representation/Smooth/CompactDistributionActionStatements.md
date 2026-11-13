# Compactly supported distributions act on smooth representations (Renard III.1.3): statements

Module `Langlands.Representation.Smooth.CompactDistributionActionStatements`. Namespace
`Langlands`. Universe parameters `u` (the group) and `v` (the representation space).
The module contains two **statements**, the `Prop`-valued definitions
`CompactDistributionActionStatement` and `LeftRegularCompactDistributionStatement`. It proves
nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. III.1.3 makes every smooth representation a module
over the algebra `ℰ′(G)` of compactly supported distributions, and only then restricts it to
the Hecke algebra `H(G)`. The Library has the restricted action (`Hecke.heckeAction`, the
III.1.3 Remark and the III.1.4 Theorem) and the algebra `ℰ′(G)` itself
(`Distribution.compactlySupported` with `convolution` and `compactDirac`, II.3.10;
[Convolution](../../HarmonicAnalysis/Distribution/Convolution.md)). No published declaration
lets `ℰ′(G)` act on a representation. The published `LeftRegularHeckeActionStatement` gives
the III.1.3 Example for `T ∈ H(G)` only.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read III.1.3, printed p.59 / PDF p.65:

> Etant donnée une représentation lisse `(π, V)` de `G`, et un élément `T` de `ℰ′(G)`, on
> définit sur `V` l'opérateur `π(T)` de la façon suivante. Soit `φ_v : G → V`,
> `g ↦ π(g) · v`. C'est une fonction localement constante à valeurs dans `V` […]. La dualité
> entre `𝒞^∞(G, V)` et `ℰ′(G)` […] permet de définir
> `π(T) · v = ⟨T, φ_v⟩ = ∫_G π(g) · v dT(g)`. On vérifie aisément que :
> `π(T₁ ∗ T₂) = π(T₁) ∘ π(T₂)`, `π(δ_g) = π(g)`, `(T₁, T₂ ∈ ℰ′(G))`, `(g ∈ G)`.
> Ceci définit une structure de `ℰ′(G)`-module (et par restriction, de `H(G)`-module) sur `V`.
>
> Exemple. Considérons la représentation lisse `(l, 𝒟(G))`. Alors pour tout `T ∈ ℰ′(G)`, pour
> tout `f ∈ 𝒟(G)`, `l(T) · f = T ∗ f`.

## Published objects used

- `Distribution.compactlySupported`: the compactly supported distributions `ℰ′(G)`;
  `Distribution.convolution` and `Distribution.compactDirac` (II.3.10).
- `Distribution.compactSupportFunctional T : LocallyConstant G ℂ →ₗ[ℂ] ℂ`: the pairing of a
  compactly supported distribution with all locally constant functions, `⟨T, φ⟩` (II.1.2;
  [CompactSupportPairing](../../HarmonicAnalysis/Distribution/CompactSupportPairing.md)).
- `Distribution.leftConvolveTest T f x = T(y ↦ f(y⁻¹ x))`, the function `T ∗ f`.
- `GroupAction.leftTests`: the left regular representation `l(g) f (x) = f(g⁻¹ x)` on test
  functions; `IsSmooth`.

## The statements

Let `G` be a t.d. group (Hausdorff, locally compact, totally disconnected).

**`CompactDistributionActionStatement`.** For a smooth complex representation `(ρ, V)` there is
a linear map `T ↦ ρ(T)` from `ℰ′(G)` to `End_ℂ(V)` such that

1. `ℓ(ρ(T) v) = ⟨T, g ↦ ℓ(ρ(g) v)⟩` for every linear form `ℓ` on `V` (stated for every
   locally constant `φ` equal to `g ↦ ℓ(ρ(g) v)`);
2. `ρ(T₁ ∗ T₂) = ρ(T₁) ρ(T₂)`;
3. `ρ(δ_g) = ρ(g)`.

**`LeftRegularCompactDistributionStatement`.** If `T ↦ l(T)` satisfies 1 for the left regular
representation on test functions, then `(l(T) f)(x) = (T ∗ f)(x) = ⟨T, y ↦ f(y⁻¹ x)⟩`.

## Formalization choices

- **The vector-valued pairing.** Renard pairs `T` with the `V`-valued locally constant
  function `φ_v`. Clause 1 characterizes this pairing through all linear forms `ℓ`. Linear forms
  separate the vectors of `V`, so clause 1 determines `ρ(T)`; the statement asserts its existence
  and its two algebraic properties.
- **The orbit function.** `g ↦ ℓ(ρ(g) v)` is locally constant because `v` is a smooth vector.
  Clause 1 quantifies over every locally constant `φ` with these values instead of building it.
- **The Example.** It is stated for any map satisfying clause 1 for `l`. By the uniqueness just
  noted, this is the action of the first statement. The restriction to `H(G)` is the published
  `LeftRegularHeckeActionStatement`.
- **Restriction to `H(G)`.** That `ρ(f μ) = heckeAction μ ρ f` for test functions `f` is not
  restated; it follows from clause 1 and the published integrated-action formula.

## Why the statements are true

Fix `v` and a compact open subgroup `K` fixing `v`. The support of `T` is covered by finitely
many cosets `g_i K`, and `φ_v` is constant on each. Put
`ρ(T) v = Σ_i T(1_{g_i K}) ρ(g_i) v`. This does not depend on the choices, is linear in `T`
and `v`, and satisfies clause 1. For clause 2, `T₁ ∗ T₂` pairs with `φ_v` as
`T₁ ⊗ T₂` pairs with `(x, y) ↦ ρ(x y) v = ρ(x) ρ(y) v`, which gives `ρ(T₁) ρ(T₂) v`. Clause 3
is the case where `T` is a point mass. For the Example take `ℓ` to be evaluation at `x`:
`ℓ(l(g) f) = f(g⁻¹ x)`, so `(l(T) f)(x) = ⟨T, g ↦ f(g⁻¹ x)⟩ = (T ∗ f)(x)`.

## Remaining obligations

The proofs are a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.HarmonicAnalysis.Distribution.Convolution` | `compactlySupported`, `convolution`, `compactDirac`, `compactSupportFunctional`, `leftConvolveTest`; through its imports `GroupAction.leftTests`, `SchwartzBruhat` |
| `Langlands.Representation.Smooth.Definitions` | `IsSmooth` |
