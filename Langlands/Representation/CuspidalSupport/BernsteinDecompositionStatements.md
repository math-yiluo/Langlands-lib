# The Bernstein decomposition theorem: statements

Module `Langlands.Representation.CuspidalSupport.BernsteinDecompositionStatements`.
Namespace `Langlands.CuspidalSupport`.
Entry proposition `BernsteinDecompositionStatements`; nothing is proved here.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read VI.7.1–VI.7.4, printed pp.180–186 / PDF pp.186–192. The
assertions stated here are on printed pp.181–184 / PDF pp.187–190.

For a connected component `Ω` of `Ω(G)` and a smooth `(π, V)`, `V(Ω)` is the
largest subrepresentation all of whose irreducible subquotients lie in
`Irr(G)_Ω`, and `(π, V)` is *split along `Ω(G)`* if `V = ⊕_Ω V(Ω)` (A.IX).

> **Théorème.** Toute représentation `(π, V)` dans `M(G)` est scindée selon
> `Ω(G)`. La catégorie `M(G)` se décompose en un produit de catégories :
> `M(G) = ∏_Ω M(G)_Ω`, où `M(G)_Ω` est la sous-catégorie pleine de `M(G)` des
> représentations dont tous les sous-quotients irréductibles sont dans
> `Irr(G)_Ω`.

> **Lemme.** Si `V′` est une sous-représentation de `V`, et que `V` est scindée
> selon `Ω(G)`, alors `V′` est scindée selon `Ω(G)`.

The end of the proof restates the Theorem with the inertial supports
`𝔰 ∈ B(G)`, which parametrize the components of `Ω(G)`: every `V` is
`V = ⊕_{𝔰 ∈ B(G)} V_𝔰` (VI.7.2.2), `Hom_G(V_𝔰, W_𝔱) = 0` for `𝔰 ≠ 𝔱`, and
`M(G) = ∏_{𝔰 ∈ B(G)} M(G)_𝔰` (VI.7.2.3). After the proof:

> Remarquons au passage que comme `M(G)_Ω` est stable par passage aux
> sous-quotients, c'est une catégorie abélienne.

The section's other assertions are not stated here; see "Scope".

## The objects

All objects are published; this file constructs nothing. The framework is the
standard-family construction of Worker 1153 (modules `BernsteinData` and
`BernsteinBlock`), already used by the published VI.10 statements
`BernsteinBlockCenterStatements` and `BernsteinBlockHomEquivalenceStatement`.

- `F : Type uF` is a nonarchimedean local field (`[Field F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F]`), `G` a group scheme over
  `Spec F` with `[IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]`, and
  `G(F) = rationalPoints G` carries the canonical topology `pointTopology`,
  with `[LocallyCompactSpace]` and `[NonarchimedeanGroup]` as hypotheses.
- `T`, `i : T.toGrp ⟶ G`, `ν : cocharacterLattice T` and
  `family : BernsteinStandardFamily i ν` give the actual standard family: the
  Prop-valued structure records connected reductivity, maximality of the split
  torus, genericity of `ν`, finiteness of the simple roots, and the
  semidirect decompositions and closedness of the standard parabolics, Levis
  and unipotent radicals. These are structural hypotheses about actual
  subgroups; they contain no representation-theoretic input.
- `B(G)` is `BernsteinInertialClass.{uF, max uF uV} i ν family`: the quotient of
  the actual cuspidal data `(M_I, ρ)` (a standard Levi and an irreducible smooth
  representation with vanishing proper standard Jacquet modules, carriers in
  `max uF uV`) by the proved inertia relation `g M₁ g⁻¹ = M₂`, `ρ₂ ≃ ρ₁^g ⊗ ω`
  with `ω` an unramified character.
- `M(G)_𝔰` is `bernsteinBlockProperty.{uF, uV} i ν family 𝔰` on
  `SmoothRep.{0, uF, uV} ℂ (rationalPoints G)`: every irreducible actual
  subquotient `π` of `V`, lifted to the universe `max uF uV`, has inertial
  support `𝔰`, i.e. is a subquotient of the normalized induction of some
  cuspidal datum of class `𝔰`. `BernsteinBlock 𝔰` is its full subcategory.
  This is Renard's `M(G)_Ω`, with `Irr(G)_Ω` expressed by the induction
  occurrence of the published `IsBernsteinInertialSupport`.
- `∏` is the published `Renard.IsCategoryDecomposition` (A.IX): every object is
  the vertex of a coproduct cofan with one component in each `M(G)_𝔰`
  (`EveryObjectIsCoproductOfComponents`), and every morphism between objects of
  distinct components is zero (`OffDiagonalHomsZero`). "Split along `Ω(G)`" for
  one object is the published `Renard.IsCoproductOfComponents`.

## The Lean statements

All three quantify over the data above, with independent universes `uF`
(field and group) and `uV` (carriers).

### `BernsteinDecompositionStatement` (VI.7.2, Theorem; (VI.7.2.2)–(VI.7.2.3))

`Renard.IsCategoryDecomposition (fun 𝔰 => bernsteinBlockProperty i ν family 𝔰)`
in `SmoothRep.{0, uF, uV} ℂ (rationalPoints G)`. Its first half says that every
smooth representation is split along the inertial classes, `V = ⊕_𝔰 V_𝔰` with
`V_𝔰 ∈ M(G)_𝔰`; its second half is `Hom_G(V_𝔰, W_𝔱) = 0` for `𝔰 ≠ 𝔱`. Together
they are `M(G) = ∏_{𝔰 ∈ B(G)} M(G)_𝔰`.

The zero representation lies in every block, so empty components are allowed,
as for the source's direct sum.

### `BernsteinSplitSubrepresentationStatement` (VI.7.2, first Lemma)

For every smooth `V` and every subrepresentation `S`, if
`Renard.IsCoproductOfComponents (bernsteinBlockProperty i ν family) V`, then
the same holds for `SmoothRep.subrepresentation V S`. The source proves it as a
case of the Lemma of A.IX; it is a step of the proof of the Theorem.

### `BernsteinBlockAbelianStatement` (remark after the proof of the Theorem)

For every inertial class `𝔰` there is an `Abelian` structure on
`BernsteinBlock 𝔰` whose preadditive structure is the inherited one. The
stability of the blocks under subquotients is already published
(`bernsteinBlockProperty_of_isSubquotient`) and is not restated.

### `BernsteinDecompositionStatements`

The conjunction of the three statements.

## Formal choices

- The decomposition is indexed by `B(G)` (inertial classes of cuspidal data),
  as in (VI.7.2.3), rather than by the connected components of the variety
  `Ω(G)`. The source identifies the two in the VI.7.1 Theorem; the variety
  structure is not available in the Library.
- Cuspidal data are those of the actual standard family; the comparison of the
  standard-family cuspidality with supercuspidality for all parabolics and the
  uniqueness of cuspidal support are recorded as obligations in
  `BernsteinBlock`. The Theorem implies that the induction-occurrence supports
  partition the irreducible representations; that is part of what a proof
  must supply, not a hypothesis.
- The carrier universe of the decomposed category is arbitrary (`uV`); the
  class index uses carriers in `max uF uV`, matching `bernsteinBlockProperty`.

## Scope

This file states three assertions of VI.7.2 and proves none of them. Proofs
belong to a separate `lean.proof@1` task targeting
`BernsteinDecompositionStatements`. The source's proof uses the functors
`I : Cusp(G) → M(G)` and `R : M(G) → Cusp(G)`, (VI.7.2.1), VI.5.3 (iii),
VI.5.4, VI.6.1–VI.6.4 and the first Lemma.

Not stated here, and remaining for later units: the second Lemma of VI.7.2
(adjunction, exactness, faithfulness of `R` and `I`, injectivity of
`V → IR(V)`), which needs the category `Cusp(G)` and the cuspidal-part
functors; the Proposition of VI.7.2 (three characterizations of `M(G)_Ω`); the
VI.7.3 Proposition (behaviour under `i_P^G` and `r_P^G`), which needs the
Bernstein data of a Levi; the central idempotents and Hecke algebra
decomposition of VI.7.4; and the variety structure of the VI.7.1 Theorem.

The file imports `Langlands.Representation.CuspidalSupport.BernsteinBlock`,
`Langlands.Representation.Category.Abelian` (the abelian structure of
`SmoothRep`) and `Langlands.CategoryTheory.RenardCategoryDecomposition`
(environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).
