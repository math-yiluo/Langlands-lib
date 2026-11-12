# Central idempotents of the Bernstein decomposition: statements

Module `Langlands.Representation.CuspidalSupport.BernsteinCentralIdempotentStatements`.
Namespace `Langlands.CuspidalSupport`.
Entry proposition `BernsteinCentralIdempotentStatements`; nothing is proved here.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.7.1–VI.7.5, printed pp.180–187 / PDF pp.186–193. The
assertions stated here are in VI.7.4, "Idempotents centraux", printed
pp.185–186 / PDF pp.191–192:

> Le théorème de décomposition permet d'écrire la catégorie `M(G)` comme un
> produit de catégories plus petites, paramétrées par les composantes connexes
> de la variété algébrique `Ω(G)`. Pour toute composante connexe `Ω` de `Ω(G)`,
> la projection `e_Ω : M(G) → M(G)_Ω` définit un idempotent du centre de la
> catégorie `M(G)` et `Id_{M(G)} = ∑_Ω e_Ω`.
> Si le support d'inertie de `Ω` est `𝔰 ∈ B(G)`, on note aussi `e_𝔰 = e_Ω`.
> L'algèbre de Hecke `H(G)` se décompose donc en
> `H(G) = ⊕_{𝔰 ∈ B(G)} e_𝔰 ∗ H(G) ∗ e_𝔰`.
> Chaque `e_𝔰 ∗ H(G) ∗ e_𝔰` est un idéal bilatère de `H(G)`. La catégorie
> `M(G)_𝔰` est équivalente à la catégorie `M(e_𝔰 ∗ H(G) ∗ e_𝔰)` des
> `e_𝔰 ∗ H(G) ∗ e_𝔰`-modules non dégénérés.

The conventions used are: the centre of a category (A.X, printed p.269 /
PDF p.275); the decomposition of a category (A.IX, printed p.268 / PDF p.274);
the Bernstein decomposition `M(G) = ∏_{𝔰 ∈ B(G)} M(G)_𝔰` (VI.7.2, printed
pp.181–184 / PDF pp.187–190); the left regular representation on test
functions, which is smooth (III.1.2, Proposition, printed pp.58–59 /
PDF pp.64–65), and on which the Hecke algebra acts by left convolution
(III.1.3, Example, printed p.59 / PDF p.65); and the equivalence of `M(G)` with
nondegenerate `H(G)`-modules (III.1.4, Theorem, printed p.60 / PDF p.66). The
completion of I.1.3 (printed pp.8–9 / PDF pp.14–15) contains the `e_𝔰`; this
file does not use it (see "Formal choices").

## The objects

All objects are published; this file constructs nothing. The setting is that
of the companion VI.7.2 statement unit `BernsteinDecompositionStatements`
(Worker 1222), on the standard-family framework of Worker 1153 (modules
`BernsteinData` and `BernsteinBlock`):

- `F : Type uF` is a nonarchimedean local field, `G` a group scheme over
  `Spec F` with `[IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]`, and
  `G(F) = rationalPoints G` carries the canonical topology `pointTopology`,
  with `[LocallyCompactSpace]` and `[NonarchimedeanGroup]` as hypotheses.
- `T`, `i`, `ν` and `family : BernsteinStandardFamily i ν` give the actual
  standard family (structural hypotheses only, no representation-theoretic
  input).
- `B(G)` is `BernsteinInertialClass.{uF, max uF uV} i ν family`, the inertial
  classes of actual cuspidal data.
- `M(G)_𝔰` is `bernsteinBlockProperty i ν family 𝔰` (every irreducible
  subquotient has inertial support `𝔰`), and `BernsteinBlock 𝔰` its full
  subcategory.
- The centre of `M(G)` is Mathlib's `CatCenter (SmoothRep ℂ G(F))`,
  `End (𝟭 _)`. An element `z` has components `z.app V : V ⟶ V`, natural in
  `V`; `SmoothRep.hom (z.app V)` is the underlying linear map.
- `H(G)` is the published `Hecke.HeckeAlgebra haar`: test functions on `G(F)`
  with convolution for a left Haar measure `haar`.
- The left regular representation is the published
  `HarmonicAnalysis.GroupAction.leftTests`, `(λ(g) f)(x) = f(g⁻¹ x)` on test
  functions. `SmoothRep.of leftTests hl` bundles it with a smoothness proof
  `hl`, and `SmoothRep.universeLift.{uV}` lifts its carrier to
  `Type (max uF uV)` (a `ULift`).
- `Algebra.NondegenerateModuleCat A` is Renard's `M(A)` for a nonunital ring
  `A`, with inclusion `Algebra.nondegenerateInclusion A` into all modules.
  `Algebra.NonUnitalModuleRestrictScalars.functor φ` restricts an action along
  a nonunital ring homomorphism `φ`. `Hecke.heckeNondegenerateModuleFunctor`
  sends a smooth representation to its carrier with the integrated Hecke
  action (III.1.4).

## The Lean statements

### `BernsteinCentralIdempotentStatement` (VI.7.4, first paragraph)

At an arbitrary carrier universe `uV`: there is a family
`e : B(G) → CatCenter (SmoothRep.{0, uF, uV} ℂ G(F))` such that

1. every `e 𝔰` is idempotent;
2. `(e 𝔰).app V = 𝟙 V` for every `V ∈ M(G)_𝔰`;
3. `(e 𝔰).app V = 0` for every `V ∈ M(G)_𝔱` with `𝔱 ≠ 𝔰`;
4. for every smooth `V` and every `v ∈ V`, the set of `𝔰` with
   `e_𝔰 v ≠ 0` is finite and `∑ᶠ 𝔰, e_𝔰 v = v`.

Conditions 2 and 3 say that `e_𝔰` is the projection onto `M(G)_𝔰`. By the
decomposition of VI.7.2 they determine `e_𝔰` on every object, hence
uniquely; this uniqueness is not stated. Condition 4 is
`Id_{M(G)} = ∑_𝔰 e_𝔰`. The sum is infinite, so it is stated vector by vector.

### `BernsteinHeckeIdealDecompositionStatement` (VI.7.4, Hecke algebra)

This statement is at carriers in `Type (max uF uV)`, the universe where the
lifted left regular representation `Λ` lives. Its hypotheses are:

- a left Haar measure `haar` on `G(F)`;
- `hl`, smoothness of the left regular representation (Renard III.1.2);
- a family `e : B(G) → CatCenter (SmoothRep.{0, uF, max uF uV} ℂ G(F))` with
  conditions 2 and 3 above (projections onto the blocks).

The conclusion is that there are nonunital subrings
`S : B(G) → NonUnitalSubring (HeckeAlgebra haar)` such that:

1. **`S 𝔰 = e_𝔰 ∗ H(G)`.** `f ∈ S 𝔰` iff `f = e_𝔰 g` for some `g ∈ H(G)`, where
   `e_𝔰 g` is the action of `(e 𝔰).app Λ` on `g` (through `ULift.up` and
   `toTestFunction`).
2. **Two-sided ideals.** `a * f ∈ S 𝔰` and `f * a ∈ S 𝔰` for all `a ∈ H(G)` and
   `f ∈ S 𝔰`.
3. **Direct sum.** `DirectSum.IsInternal (fun 𝔰 => (S 𝔰).toAddSubgroup)`:
   `H(G) = ⊕_𝔰 S 𝔰`. A classical decidable equality on `B(G)` is supplied,
   as `DirectSum.IsInternal` requires one; the property does not depend on it.
4. **Equivalence.** For each `𝔰` there is an equivalence
   `E : BernsteinBlock 𝔰 ≌ NondegenerateModuleCat (S 𝔰)`, and an isomorphism
   between `E.functor ⋙ nondegenerateInclusion (S 𝔰)` and the composite
   `ι ⋙ heckeNondegenerateModuleFunctor haar ⋙ nondegenerateInclusion H(G) ⋙
   NonUnitalModuleRestrictScalars.functor (NonUnitalSubringClass.subtype (S 𝔰))`.
   That is, up to isomorphism, `E` sends `V ∈ M(G)_𝔰` to its Hecke module with
   the action restricted to `S 𝔰`.

The family `e` is a hypothesis rather than an existential witness, so this
statement does not depend on the existential of the first statement. Any `e`
satisfying the hypotheses is the family of block projectors, and the first
statement (at the universe `max uF uV`) says that such a family exists.

### `BernsteinCentralIdempotentStatements`

The conjunction of the two statements.

## Formal choices

- **`e_𝔰 ∗ H(G) ∗ e_𝔰` as `e_𝔰 ∗ H(G)`.** Renard's `e_𝔰` lies in the completion
  of `H(G)` (I.1.3), which acts on `H(G)` by left multiplication. Through
  III.1.4 and III.1.3 (`λ(T) f = T ∗ f`), left multiplication by a central
  element of the completion is its action, as an element of the centre of
  `M(G)`, on the left regular representation. That action is
  `(e 𝔰).app Λ`. Since `e_𝔰` is a central idempotent,
  `e_𝔰 ∗ f ∗ e_𝔰 = e_𝔰 ∗ f`. Hence `S 𝔰`, the image of `(e 𝔰).app Λ`, is
  Renard's `e_𝔰 ∗ H(G) ∗ e_𝔰`. The completion itself, and the identification
  of the centre of `M(G)` with its centre, are not used.
- **Smoothness of `λ` as a hypothesis.** It is Renard's III.1.2 Proposition,
  published as part of `RegularRepresentationSmoothStatement`. It is taken as
  the hypothesis `hl`, as in the published `LeftRegularHeckeActionStatement`.
  It is a true assertion, so the statement is not weakened in substance.
- **Universes.** The first statement is at an arbitrary carrier universe. The
  second is at `max uF uV`, because the test functions on `G(F)` lie in
  `Type uF` and are lifted.
- **Ideals as subrings.** A two-sided ideal is a nonunital subring stable
  under multiplication by `H(G)` on both sides. The subring structure is what
  gives `S 𝔰` the nonunital ring needed for `NondegenerateModuleCat (S 𝔰)`.
  Membership is characterized exactly by condition 1.
- **The equivalence functor.** The source asserts only that the categories are
  equivalent. The intended functor (restriction of the Hecke action) is
  specified up to isomorphism, which makes the equivalence the canonical one.
- **Index set.** As in VI.7.2, the decomposition is indexed by `B(G)`; the
  variety structure of `Ω(G)` (VI.7.1 Theorem) is not available.

## Scope

This file states the assertions of the VI.7.4 paragraph quoted above and
proves none of them. Proofs belong to a separate `lean.proof@1` task targeting
`BernsteinCentralIdempotentStatements`. The first statement follows from the
Bernstein decomposition (`BernsteinDecompositionStatement`) by the A.IX
argument. For two factors, the published module
`Langlands.CategoryTheory.Renard.DecompositionCenterIdempotent` (Worker 1842)
carries out that argument.

Not stated:

- The Remark that `e_𝔰` is not an element of `H(G)` but of its completion.
  Read literally, it fails when `G(F)` is compact: then every `e_𝔰` is
  `dim ρ` times the conjugate character of an irreducible `ρ`, a test
  function. The remark describes the general situation, not a theorem.
- The program sketched after the Remark (progenerators of `M(G)_Ω` and the
  centre of `M(G)_Ω`), which is carried out in VI.10. The VI.10 results are
  stated in the published `BernsteinBlockCenterStatements` and related units.

The file imports `Langlands.Representation.CuspidalSupport.BernsteinBlock`,
`Langlands.Representation.Category.Abelian` (the preadditive structure of
`SmoothRep`), `Langlands.Representation.Hecke.NondegenerateModuleFunctor`,
`Langlands.Algebra.NonUnitalModuleRestrictScalars`,
`Langlands.HarmonicAnalysis.GroupAction`, and Mathlib's
`CategoryTheory.Center.Basic`, `Algebra.DirectSum.Basic` and
`RingTheory.NonUnitalSubring.Basic` (environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).
