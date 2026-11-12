# Smooth representations and nondegenerate Hecke modules (Renard III.1.4, Theorem): statement

Author: Worker 1222. Module `Langlands.Representation.Hecke.NondegenerateModuleEquivalenceStatement`,
namespace `Langlands.Hecke`. The module contains one **statement**, the closed `Prop`-valued
definition `HeckeNondegenerateModuleEquivalenceStatement` (universe parameters `u, v`). It
proves nothing.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
**9 July 2026**, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Worker 1222 read
III.1.1–III.1.6, printed pp.58–62 / PDF pp.64–68, for this unit. The Theorem of III.1.4,
printed p.60 / PDF p.66, reads:

> **Théorème.** Si `(π, V)` est une représentation lisse de `G`, le `H(G)`-module `V` est non
> dégénéré. Réciproquement, tout `H(G)`-module `V` non dégénéré définit une représentation
> lisse de `G`. Ces deux opérations sont inverses l'une de l'autre et induisent une
> équivalence de catégories entre `M(G)` et `M(H(G))`.

Here `M(G)` is the category of smooth representations of the t.d. group `G` with the
intertwining operators (III.1.3), `H(G)` its Hecke algebra (II.3.12), and `M(H(G))` the
category of nondegenerate `H(G)`-modules (I.1.2). The proof notes that a vector fixed by a
compact open `K` is fixed by the idempotent `e_K`, and recovers the action of `G` on a
nondegenerate module through `T · v := (T ∗ e_K) · v` for distributions `T`, in particular
`T = δ_g`.

## Published objects used

From [NondegenerateModuleFunctor](NondegenerateModuleFunctor.md) (module
`Langlands.Representation.Hecke.NondegenerateModuleFunctor`):

- `HeckeAlgebra μ`, the published Haar Hecke algebra of compactly supported locally constant
  functions with convolution for the left Haar measure `μ`, a nonunital ring; Renard
  identifies `𝒟(G)` with `H(G)` through `f ↦ f μ_G` (III.1.3, Remark);
- `heckeNondegenerateModuleFunctor μ : SmoothRep.{0, u, v} ℂ G ⥤
  Algebra.NondegenerateModuleCat.{u, v} (HeckeAlgebra μ)`, the functor of the Theorem: a
  smooth representation goes to its carrier with the integrated action
  `f • v = ∫ f(g) ρ(g) v dμ(g)`, and an intertwiner to the same additive map. The first
  sentence of the Theorem (nondegeneracy) is the published theorem
  `heckeNonUnitalModule_isNondegenerate`, used to build this functor.

From Mathlib: `CategoryTheory.Functor.IsEquivalence`.

## Lean statement

`HeckeNondegenerateModuleEquivalenceStatement` quantifies over a group `G : Type u` with a
topology, `[T2Space G]`, `[NonarchimedeanGroup G]`, `[LocallyCompactSpace G]`, a measurable
structure with `[BorelSpace G]`, and a measure `μ` with `[μ.IsHaarMeasure]`. These are the
hypotheses of the published functor together with the Hausdorff property, so that `G` is a
t.d. group in the sense of Renard. It asserts

```lean
(heckeNondegenerateModuleFunctor.{u, v} μ).IsEquivalence
```

for the carrier universe `v`, which is independent of `u`.

## Provenance and departures from the source

The provenance is the source Theorem.

- **t.d. groups.** Renard II.1.1, printed p.30 / PDF p.36, defines a t.d. space as a Hausdorff
  ("séparé") space in which every point has a basis of compact open neighbourhoods, and a t.d.
  group as a topological group whose underlying space is t.d.; he notes that it suffices, and
  by van Dantzig's theorem is necessary, that the identity have a basis of compact open
  subgroups. For a topological group this is the conjunction of `[T2Space G]`,
  `[LocallyCompactSpace G]` and `[NonarchimedeanGroup G]`: these give a basis of compact open
  subgroups at the identity (the published `Langlands.compactOpenSubgroupBasis`), and
  conversely, by van Dantzig's theorem, a t.d. group is locally compact and has open subgroups
  in every neighbourhood of the identity. The Hausdorff hypothesis is kept explicitly, since `NonarchimedeanGroup`,
  `LocallyCompactSpace`, `BorelSpace` and `IsHaarMeasure` do not imply it (a nontrivial finite
  group with the indiscrete topology satisfies them). The published functor itself is
  constructed without the Hausdorff hypothesis; the statement only restricts its domain of
  quantification to the source's groups.
- **`H(G)`.** The published Hecke algebra depends on the chosen Haar measure `μ`; the source
  makes the same identification `𝒟(G) ≅ H(G)` through `μ_G`.
- **"Inverses l'une de l'autre".** The two constructions of the source keep the same
  carrier. The statement asserts the equivalence of categories, which is the conclusion the
  source draws; the inverse functor is not named. Its essential image is everything because
  every nondegenerate module carries a smooth representation on the same carrier.
- **Coefficients.** The target category consists of nondegenerate modules over the ring
  `H(G)`, without a separately specified complex structure, as in Chapter I. A morphism of
  the target is an additive `H(G)`-equivariant map; between smooth representations such a
  map is automatically complex-linear and `G`-equivariant, because `c v = (c e_K) · v` and
  `g v = (δ_g ∗ e_K) · v` for `v` fixed by `K`.

## Scope

This module states the Theorem of III.1.4 and proves none of it. The construction of the
functor and its nondegeneracy are the published definition unit. A proof belongs to a
separate proof task.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Hecke.NondegenerateModuleFunctor` | `HeckeAlgebra`, `heckeNondegenerateModuleFunctor`, and through it `SmoothRep` and `Algebra.NondegenerateModuleCat` |
