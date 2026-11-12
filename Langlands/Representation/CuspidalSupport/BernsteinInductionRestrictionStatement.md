# Bernstein decomposition, induction and restriction: statement

Module `Langlands.Representation.CuspidalSupport.BernsteinInductionRestrictionStatement`.
Namespace `Langlands.CuspidalSupport`.
Entry proposition `BernsteinInductionRestrictionStatement`; nothing is proved here.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.7.1–VI.7.4, printed pp.180–186 / PDF pp.186–192. The
statement is the Proposition of VI.7.3, printed p.185 / PDF p.191:

> Soit `P = MN` un sous-groupe parabolique de `G`. Une donnée cuspidale
> `(L, (σ, E))` de `M` est aussi une donnée cuspidale pour `G`, puisqu'un
> sous-groupe de Levi de `M` est aussi un sous-groupe de Levi de `G`, et l'on a
> donc une application `i_{MG} : Ω(M) → Ω(G)`,
> `(L, (σ, E))_M ↦ (L, (σ, E))_G`. Cette application en induit une autre, notée
> de la même façon, entre ensembles de supports d'inertie :
> `i_{MG} : B(M) → B(G)`, `[L, (σ, E)]_M ↦ [L, (σ, E)]_G`.
>
> **Proposition.** Soit `𝔰 ∈ B(M)` et soit `(ρ, W)` dans `M(M)_𝔰`. Alors
> `i_P^G(ρ, W)` est dans `M(G)_{i_{MG}(𝔰)}`. Soit `𝔱 ∈ B(G)` et soit `(π, V)`
> dans `M(G)_𝔱`. Alors `r_P^G(π, V)` est dans
> `∏_{𝔰 ∈ i_{MG}^{-1}(𝔱)} M(M)_𝔰`.
>
> *Démonstration.* Ceci découle directement des caractérisations des
> représentations de `M(M)_𝔰` et `M(G)_{i_{MG}(𝔰)}` obtenues dans la section
> précédente.

Here, as in the Theorem of VI.7.2 (printed p.182 / PDF p.188), `M(G)_𝔱` is the
full subcategory of the smooth representations all of whose irreducible
subquotients have inertial support `𝔱`, and likewise for `M(M)_𝔰`.

## The objects

All objects are published; this file constructs nothing. The setting is that
of the companion VI.7.2 statement units `BernsteinDecompositionStatements` and
`BernsteinBlockCharacterizationStatement` (Worker 1222), on the standard-family
framework of Worker 1153 (modules `BernsteinData` and `BernsteinBlock`).

- `F`, `G`, `T`, `i`, `ν` and `family : BernsteinStandardFamily i ν` are as in
  those units: a nonarchimedean local field, a group scheme with locally
  compact nonarchimedean `G(F)` in the canonical topology, and the actual
  standard family (structural hypotheses only).
- `J : Finset (SimpleRoot i ν)` gives the standard parabolic
  `P = parabolic i ν J` with Levi `M = levi i ν J` and radical
  `N = unipotent i ν J`, all subgroups of `G(F)`.
- `a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family` is a cuspidal datum
  of `G`; `𝔱` is its class `bernsteinInertialClass i ν family a`, and
  `M(G)_𝔱` is `bernsteinSaturatedBlockProperty i ν family 𝔱`.
- `ind` is `i_P^G`, the published `normalizedInductionFunctor` for
  `P = M ⋉ N`, and `jac` is `r_P^G`, the published `normalizedJacquetFunctor`
  along `N`, used in the same way as in the published
  `BernsteinBlockCharacterizationStatement`.
- For `I : Finset J`, the standard Levi `M_K` with `K = leviIndex J I ⊆ J` has
  the parabolic `P_K ∩ M = M_K ⋉ (N_K ∩ M)` of `M`; this is the field
  `family.leviDecomposition J I`. Normalized induction inside `M` from `M_K` is
  the published `leviNormalizedInductionFunctor` (transport along
  `M_K ∩ M ≃ M_K`, then normalized induction inside the closed subgroup `M`).
  It needs `M_K ≤ M`, supplied by the published `levi_le_of_subset` applied to
  the proved `standardLeviIntersection`.

## The Lean statement

The *fibre property* `fibre` of a smooth representation `ρ` of `M(F)` says:
every irreducible subquotient `τ` of `ρ` is a subquotient of
`i^M_{M_K}(σ)` for some cuspidal datum `b = (M_K, σ)` of `G` with
`K = b.roots = leviIndex J I` for some `I : Finset J`, such that
`IsBernsteinInertiaRelated i ν family a b`. Here `σ` is transported to the
literal Levi by `bernsteinLiteralLeviRep`, as in the published
`bernsteinInduction`.

`BernsteinInductionRestrictionStatement` quantifies over the data above and
asserts:

1. for every `ρ : SmoothRep.{0, uF, max uF uV} ℂ M(F)` with `fibre ρ`,
   `i_P^G(ρ)` lies in `M(G)_𝔱`;
2. for every `V : SmoothRep.{0, uF, max uF uV} ℂ G(F)` in `M(G)_𝔱`,
   `fibre (r_P^G(V))` holds.

## Why the fibre property is Renard's

- **Cuspidal data of `M`.** A cuspidal datum of `M` is a Levi subgroup `L` of
  `M` with an irreducible supercuspidal representation of `L`. Up to
  `M`-conjugacy `L` is a standard Levi `M_K` of `M`, `K ⊆ J`. Supercuspidality
  of a representation of `M_K` (vanishing of its proper standard Jacquet
  modules, VI.2.1, printed p.137 / PDF p.143) concerns `M_K` alone. So the
  cuspidal data of `G` with `b.roots ⊆ J` are exactly the standard cuspidal
  data of `M`. The equation `leviIndex J I = b.roots` names `b.roots` as a
  subset of `J`; it is used only to transport proofs (the Levi inclusion and
  the decomposition), never data.
- **The fibre.** For such a datum, `i_{MG}([b]_M) = [b]_G`, so `[b]_M` lies in
  `i_{MG}^{-1}(𝔱)` exactly when `b` is inertially equivalent to `a` in `G`. An
  irreducible representation `τ` of `M(F)` has inertial support `[b]_M` when it
  is a subquotient of the induction `i^M_{M_K}(σ′)` of a datum `(M_K′, σ′)`
  `M`-equivalent to `b`; this is the induction-occurrence support of the
  published `BernsteinBlock`, applied in `M`. Hence `fibre ρ` says that every
  irreducible subquotient of `ρ` lies in `Irr(M)_𝔰` for some
  `𝔰 ∈ i_{MG}^{-1}(𝔱)`. The relation `M`-equivalence never has to be named:
  `M`-equivalent data are `G`-equivalent.
- **First assertion.** Clause 1 contains Renard's first assertion: if
  `ρ ∈ M(M)_𝔰`, choose a standard datum `a` of `M` with `[a]_M = 𝔰`; then
  `fibre ρ` holds for the `G`-class `i_{MG}(𝔰) = [a]_G`, and clause 1 gives
  `i_P^G(ρ) ∈ M(G)_{i_{MG}(𝔰)}`. Conversely, Renard's assertion implies
  clause 1. By the Bernstein decomposition of `M(M)` (VI.7.2 for `M`), an
  object with `fibre ρ` is the direct sum of its components in the `M(M)_𝔰`,
  `𝔰 ∈ i_{MG}^{-1}(𝔱)`; `i_P^G` commutes with direct sums (VI.7.2.1); and
  `M(G)_𝔱` is closed under direct sums.
- **Second assertion.** By the same decomposition of `M(M)`, the product
  `∏_{𝔰 ∈ i_{MG}^{-1}(𝔱)} M(M)_𝔰` is the full subcategory of the objects all of
  whose irreducible subquotients lie in some `Irr(M)_𝔰` of the fibre, that is,
  of the objects with `fibre`. So clause 2 is Renard's second assertion.

These comparisons use the Bernstein decomposition of `M(M)` and (VI.7.2.1).
They are not formalized; they explain why this formulation, which needs only
`G`-level data, is faithful.

## Formal choices

- **Standard parabolics.** Renard takes an arbitrary parabolic `P = MN`. The
  statement takes the standard parabolics `P_J`. An arbitrary parabolic is
  `G(F)`-conjugate to a standard one, conjugation transports induction and
  Jacquet modules, and the blocks `M(G)_𝔱` are stable under it.
- **Universe.** All carriers lie in the saturated universe `max uF uV`, the
  universe of the published saturated block and of normalized induction.
- **Support.** As in `BernsteinBlock`, inertial support is defined by
  occurrence in normalized induction. Its comparison with the cuspidal support
  defined by Jacquet modules is the support-uniqueness obligation recorded
  there.
- **Index sets.** The fibre `i_{MG}^{-1}(𝔱)` is not formed as a set: the fibre
  property quantifies over the data directly. The varieties `Ω(M)`, `Ω(G)` and
  the morphism `i_{MG}` of varieties (VI.7.1, VI.10.5) are not available.

## Scope

This file states the VI.7.3 Proposition and proves nothing. A proof belongs to
a separate `lean.proof@1` task targeting
`BernsteinInductionRestrictionStatement`. The source deduces both assertions
from the characterizations of the VI.7.2 Proposition (published as
`BernsteinBlockCharacterizationStatement`), applied in `G` and in `M`. In the
present formulation the deduction also uses the existence of cuspidal
supports of irreducible representations of `M` (VI.7.1 for `M`), induction
and Jacquet modules in stages for `M_K ⊆ M ⊆ G`, and exactness of `r_P^G`.

The file imports `Langlands.Representation.CuspidalSupport.BernsteinBlock`,
`Langlands.Representation.Aubert.General.RationalInductionStagesGeometry` and
`Langlands.GroupScheme.Rational.StandardLeviIntersectionProof` (environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).
