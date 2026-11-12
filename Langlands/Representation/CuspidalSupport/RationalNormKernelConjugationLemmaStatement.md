# Conjugation of norm-kernel representations (Renard VI.3.1, Lemma): statement

Module `Langlands.Representation.CuspidalSupport.RationalNormKernelConjugationLemmaStatement`.
Namespace `Langlands.CuspidalSupport`. Universe parameters `u, uV, uW`.
The module contains one **statement**, the `Prop`-valued definition
`RationalNormKernelConjugationLemmaStatement`; it proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.3.1 and the start of VI.3.2, printed pp.142–143 / PDF
pp.148–149:

> Comme `⁰G` est un sous-groupe distingué de `G`, `G` agit sur `Irr(⁰G)` par
> `(g, σ) ↦ σ^g` […]
>
> **Lemme.** (i) Les orbites de l'action de `G` sur `Irr(⁰G)` sont de cardinal
> fini. — (ii) Soient `(π, V)` une représentation lisse de `G`, `(σ, W)` une
> représentation lisse irréductible de `⁰G`, et `V(σ)` la composante
> `σ`-isotypique de la restriction de `(π, V)` à `⁰G`. On a alors, pour tout
> `g ∈ G`, `π(g) · V(σ) = V(σ^g)`.

The proof computes `(σ^g)(h) = σ(g⁻¹ h g)` and defines `V(σ)` as the image of
`Hom_{⁰G}(σ, π) ⊗ W → V`, `f ⊗ w ↦ f(w)`. The published VI.3.2 statements
(`RationalNormKernelOrbitStatement` and its companions) do not contain this
Lemma.

## The statement

The binders are those of the published `RationalNormKernelOrbitStatement`: a
nonarchimedean local field `F`, a connected reductive `G`, and the canonical
topology on `G(F)` with its topological group structure.
`⁰G = Plancherel.rationalCommonNormKernel G` carries its subspace topology. For
`g ∈ G(F)`, `conj g` is the automorphism `h ↦ g⁻¹ h g` of `⁰G`, written
`MulAut.conjNormal g⁻¹`. The conjugate of a representation `σ` of `⁰G` is then
`σ^g = σ ∘ conj g`.

1. For every irreducible smooth `σ : SmoothRep ℂ ⁰G` there is a finite set
   `S ⊆ G(F)` such that for every `g` some `s ∈ S` has `σ^g` equivalent to
   `σ^s`. In other words, the orbit of the class of `σ` is finite.
2. For every smooth `π : SmoothRep ℂ G(F)`, every irreducible smooth `σ` of `⁰G`
   and every `g`, the image under `π(g)` of the isotypic part
   `iso σ = span {f w | f : σ → π|_{⁰G} intertwining, w ∈ σ}` equals
   `iso (σ^g)`.

## Formalization choices

- **`Irr(⁰G)` and its orbits.** No type of isomorphism classes is introduced.
  Finiteness of the orbit of `[σ]` is stated as the existence of a finite set of
  representatives `S` for the classes `[σ^g]`.
- **Isotypic part.** `V(σ)` is the span of the images of all intertwining maps.
  This equals the image of the evaluation map
  `Hom_{⁰G}(σ, π) ⊗ W → V`. In (ii) the representation `σ^g` is the actual
  composite, not a chosen representative of its class.
- **Carriers.** `π` and `σ` have independent carrier universes `uV` and `uW`.
  Irreducibility of `σ` is kept in (ii) as in the source, although the identity
  holds for every `σ`.

## Why the statement is true

(i) Conjugation by `⁰G` gives isomorphic representations (by `σ(h)`), and the
centre acts trivially. So the action on classes factors through
`G/⁰G Z(G)`, which is finite (Proposition V.2.6). (ii) `f ↦ π(g) ∘ f` is a
bijection `Hom_{⁰G}(σ, π) ≅ Hom_{⁰G}(σ^g, π)` (source computation), so `π(g)`
maps the images onto each other.

## Remaining obligations

The proof is a separate obligation. Part (i) needs the finiteness of
`G/⁰G Z(G)` (V.2.6; check the Library for its published form).

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CuspidalSupport.RationalNormKernelOrbitTwistStatement` | the binders of the VI.3.2 statements, `Plancherel.rationalCommonNormKernel` with its topology, `SmoothRep` |
