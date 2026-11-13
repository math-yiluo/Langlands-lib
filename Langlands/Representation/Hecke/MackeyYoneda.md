# Abstract Mackey isomorphisms from currying and adjunctions

Worker 231, Task 5449.

This is an internal supporting unit for Renard III.2.11 (*Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, printed pp.82–83 /
PDF pp.88–89; registered source
`renard-2026-representations-groupes-reductifs-padiques`). It formalizes the
categorical part of the proof displays (III.2.11.1)–(III.2.11.10), the "general
argument of category theory" invoked there, in arbitrary categories. Nothing in
this file is specific to representations, and nothing here is asserted by the
source beyond that Yoneda argument.

`Homomorphism.isoOfNaturalHomEquiv`, reused from `MackeyCurrying`, and
`isoOfHomFromEquiv` are the two forms of Yoneda used. Suppose
there are bijections `(E ⟶ A j) ≃ (E ⟶ B j)` (respectively
`(A j ⟶ X) ≃ (B j ⟶ X)`) that are natural in the test object and compatible with the
maps `A u`, `B u` of the index category. Then they come from a natural isomorphism
`A ≅ B`. Its components are the images of identities under the bijections and
their inverses.

`Mackey.Currying T Hm` packages a tensor–Hom currying datum on one category `C`,
for a tensor bifunctor `T : C × C ⥤ C` and a Hom bifunctor `Hm : Cᵒᵖ × C ⥤ C`. It
consists of bijections `(T(E,V) ⟶ X) ≃ (E ⟶ Hm(V,X))` and one combined
naturality equation in `E`, `V` (contravariantly, through `Cᵒᵖ`) and `X`. The
one-variable naturality laws, and their versions for the inverse bijection, are
derived from it.

`homMackeyIso` takes curryings on `C` and `D`, an adjunction `R ⊣ I` with
`R : C ⥤ D`, and an isomorphism `μ : TC ⋙ R ≅ R.prod R ⋙ TD`. It produces a natural
isomorphism `(𝟭 Cᵒᵖ).prod I ⋙ HC ≅ R.op.prod (𝟭 D) ⋙ HD ⋙ I`, that is
`Hom(V, I W) ≅ I Hom(R V, W)`, natural in both `V` and `W`. The underlying
bijection `homMackeyEquiv` is the composite of the following steps, in this order:

1. inverse currying on `C`;
2. inverse adjunction;
3. precomposition with `μ.inv`;
4. currying on `D`;
5. the adjunction.

These are displays (III.2.11.1)–(III.2.11.5). Two lemmas prove its naturality in
the test object `E` and in the pair `(V, W)`.

`tensorMackeyIso` takes the same curryings, an adjunction `P ⊣ R` with
`P : D ⥤ C`, and an isomorphism `ν : HC ⋙ R ≅ R.op.prod R ⋙ HD`. It produces a
natural isomorphism `P.prod (𝟭 C) ⋙ TC ≅ (𝟭 D).prod R ⋙ TD ⋙ P`, that is
`P W ⊗ V ≅ P(W ⊗ R V)`, natural in both `W` and `V`. The underlying bijection
`tensorMackeyEquiv` is the composite of these steps, in this order:

1. currying on `C`;
2. the adjunction;
3. postcomposition with `ν.hom`;
4. inverse currying on `D`;
5. inverse adjunction.

These are displays (III.2.11.6)–(III.2.11.10). The isomorphism `ν` is exactly the
comparison (III.2.11.8) that the source leaves unjustified in general.

The file imports `MackeyCurrying` to reuse its existing maps-into-values
Yoneda construction, with the test-object and index arguments reordered.
The constructions in this file remain general categorical constructions.
