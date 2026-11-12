# Characterizations of a Bernstein block: statement

Module `Langlands.Representation.CuspidalSupport.BernsteinBlockCharacterizationStatement`.
Namespace `Langlands.CuspidalSupport`.
Entry proposition `BernsteinBlockCharacterizationStatement`; nothing is proved here.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.7.1–VI.7.4, printed pp.180–186 / PDF pp.186–192. The
statement is the Proposition of VI.7.2, printed p.184 / PDF p.190; its proof
continues on printed p.185 / PDF p.191:

> Fixons un sous-groupe de Levi (standard) `M` de `G` et `D = [ρ]` une classe
> d'inertie de représentations irréductibles supercuspidales de `M` tels que
> `(M, ρ)_G ∈ Ω`. Soit `P` le sous-groupe parabolique standard de `G` contenant
> `M`.
>
> **Proposition.** Une représentation `(π, V)` est dans `M(G)_Ω` si et
> seulement si l'une des conditions équivalentes suivantes est vérifiée :
> (i) `(π, V)` se plonge dans une somme de représentations de la forme
> `i_P^G(τ, E)`, avec `(τ, E) ∈ M(M)_D`.
> (ii) `(π, V)` est sous-quotient d'une somme de représentations comme en (i).
> (iii) Quels que soient le sous-groupe parabolique `Q = LU` standard de `G` et
> la classe d'inertie `D′` de représentations irréductibles supercuspidales de
> `L`, tels que `(M, D)` et `(L, D′)` ne soient pas conjuguées, la composante
> dans `M(L)_{D′}` de `r_Q^G(π, V)` est nulle.

Here `M(M)_D` is the full subcategory of `M(M)` of the representations all of
whose irreducible subquotients lie in `D` (VI.3, the component of the
supercuspidal decomposition of `M(M)`).

## The objects

All objects are published; this file constructs nothing. The setting is that
of the companion VI.7.2 statement unit `BernsteinDecompositionStatements`
(Worker 1222), on the standard-family framework of Worker 1153 (modules
`BernsteinData` and `BernsteinBlock`). The binders and the instance
declarations for the standard Levi follow the published VI.10.3 statement
`BernsteinBlockJacquetFaithfulStatement` (Worker 6).

- `F`, `G`, `T`, `i`, `ν` and `family : BernsteinStandardFamily i ν` are as in
  `BernsteinDecompositionStatements`: a nonarchimedean local field, a group
  scheme with locally compact nonarchimedean `G(F)` in the canonical topology,
  and the actual standard family (structural hypotheses only).
- `a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family` is Renard's
  `(M, ρ)`. `M` is the standard Levi scheme `bernsteinLeviScheme i ν a.roots`,
  `ρ = a.representation` is an irreducible smooth representation of `M(F)`
  with vanishing proper standard Jacquet modules, and `P` is the standard
  parabolic of `a.roots`.
- `M(G)_Ω` is `bernsteinSaturatedBlockProperty i ν family
  (bernsteinInertialClass i ν family a)`: every irreducible subquotient of `V`
  is a subquotient of the normalized induction of a cuspidal datum
  inertially equivalent to `a`.
- `M(M)_D` is the published `rationalInertiaBlockProperty M ρ`: every
  irreducible subquotient of the representation of `M(F)` is isomorphic to an
  unramified twist of `ρ`.
- `i_P^G(τ)` is `ind τ`, the published `normalizedInductionFunctor` for the
  decomposition `P = M ⋉ N` of `a.roots`, applied to `τ` transported to the
  literal standard Levi subgroup by `bernsteinLiteralLeviRep`. This is the
  same functor as in the published `bernsteinInduction`.
- A sum of representations is the published `SmoothRep.directSum` (the
  algebraic direct sum with the componentwise action), over an index type
  `κ : Type (max uF uV)`. Decidable equality on `κ` is supplied classically.
- `r_Q^G` is the published `normalizedJacquetFunctor` along the standard
  parabolic `Q = L ⋉ U` of another cuspidal datum `b`, as in
  `BernsteinBlockJacquetFaithfulStatement`.
- "Embeds in" and "subquotient of" are the published
  `SmoothRep.IsSubrepresentation` (an injective intertwiner) and
  `SmoothRep.IsSubquotient`.

## The Lean statement

`BernsteinBlockCharacterizationStatement` quantifies over the data above and
over every smooth `V : SmoothRep.{0, uF, max uF uV} ℂ G(F)`. It asserts three
equivalences:

1. `V ∈ M(G)_Ω` iff there are `κ` and `τ : κ → SmoothRep ℂ M(F)` with every
   `τ k ∈ M(M)_D` and `V` isomorphic to a subrepresentation of
   `⊕_k i_P^G(τ k)`. This is (i).
2. The same with "subquotient of" in place of "subrepresentation of". This is
   (ii).
3. `V ∈ M(G)_Ω` iff for every cuspidal datum `b` with
   `¬ IsBernsteinInertiaRelated i ν family a b`, the representation
   `b.representation` (on the literal standard Levi of `b.roots`) is not a
   subquotient of `r_Q^G(V)`, where `Q` is the standard parabolic of
   `b.roots`. This is (iii).

## Why (iii) is Renard's condition (iii)

- The pairs `(Q, D′)` of the source are a standard parabolic `Q = LU` and an
  inertial class of irreducible supercuspidal representations of `L`. The
  cuspidal data `b` of the standard family are exactly a standard Levi `L`
  (indexed by `b.roots`) and an irreducible representation `σ` of `L` whose
  proper standard Jacquet modules vanish. This is Renard's supercuspidality
  (VI.2.1, Definition: all proper Jacquet modules vanish; Remark 1: standard
  parabolics suffice), printed p.137 / PDF p.143. `D′ = [σ]`.
- "`(M, D)` and `(L, D′)` are not conjugate" is
  `¬ IsBernsteinInertiaRelated i ν family a b`: the published relation is
  conjugacy of the Levis together with an unramified twist.
- "The component of `r_Q^G(V)` in `M(L)_{D′}` is zero" is replaced by "`σ` is
  not a subquotient of `r_Q^G(V)`, for every `b = (L, σ)` not related to `a`".
  The two agree, by the following argument, which is not formalized. The
  component is a direct factor of `r_Q^G(V)`, by the decomposition
  `M(L) = M(L)_{D′} × M(L)^{D′}` of VI.3 (published as
  `RationalInertiaDecompositionStatement`). If the component is nonzero, it
  has an irreducible subquotient `σ′`, which lies in `D′`. Then `σ′` is an
  unramified twist of `σ`, hence itself irreducible and supercuspidal. So `σ′` is
  the representation of a datum `b′ = (L, σ′)` related to `b`, hence not
  related to `a`, and `σ′` is a subquotient of `r_Q^G(V)`. Conversely, if the
  component is zero, no irreducible subquotient of `r_Q^G(V)` lies in `D′`, and
  in particular `σ` is not one. Every class `D′` arises from some datum `b`.

## Formal choices

- **Universe.** `V`, the `τ k` and the cuspidal data have carriers in the
  saturated universe `max uF uV`. This is the universe of the published
  saturated block and of normalized induction from `M(F)`. Arbitrary carrier
  universes would need explicit lifts to compare `V` with the induced
  representations.
- **Index universe.** The sums in (i) and (ii) are indexed by
  `κ : Type (max uF uV)`. This loses nothing: a vector of `V` lies in finitely
  many summands, so `V` already embeds in, or is a subquotient of, a sub-sum
  indexed by a set no larger than the carrier of `V`.
- **Index set of the blocks.** As in VI.7.2, `Ω` is the inertial class of `a`
  in `B(G)`; the variety structure of `Ω(G)` (VI.7.1 Theorem) is not
  available.

## Scope

This file states the VI.7.2 Proposition and proves nothing. A proof belongs to
a separate `lean.proof@1` task targeting
`BernsteinBlockCharacterizationStatement`. The source proof reads (i) and
(iii) off the proof of the Bernstein decomposition, through the embedding
`V ↪ IR(V)` and (VI.7.2.1). It deduces (ii) ⇒ (iii) from the exactness of
`r_P^G` and the geometric lemma (VI.5.3).

Not stated here: the VI.7.3 Proposition. Its first assertion says that
`i_P^G` maps `M(M)_𝔰` into `M(G)_{i_{MG}(𝔰)}`; its second, that `r_P^G` maps
`M(G)_𝔱` into `∏_{𝔰 ∈ i_{MG}^{-1}(𝔱)} M(M)_𝔰`. It needs the Bernstein data of
the Levi `M` itself (its own cuspidal data up to `M`-conjugacy) and the map
`i_{MG}`. Neither is available in the published framework.

The file imports `Langlands.Representation.CuspidalSupport.BernsteinBlock` and
`Langlands.Representation.Category.SmoothCoproducts` (environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).
