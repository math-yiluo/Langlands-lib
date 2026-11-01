# Renard A.III.3: the object and functor isomorphism principles

This pair states the two clauses of the proposition in Renard 2026,
Appendix A.III.3. It supplies closed proposition definitions and no proofs.

## Source and conventions

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.III.3, printed p.255 /
one-based PDF261, proposition with displays (A.III.3.1) and (A.III.3.2).
Registered identifier: `renard-2026-representations-groupes-reductifs-padiques`;
SHA256:
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original page was read directly and visually inspected.

The prose places the test object Z and both displayed targets in M, but the
printed Hom subscripts say C. The Hom sets in both clauses must belong to M
for their displayed objects to have the stated types. The Lean statements
make this interpretation explicit. In the second clause, C is the source
category of the two functors and M is their target category.

The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked at PDF18–19. These pages contain corrections to nearby
representability assertions but no correction to this isomorphism principle
or its Hom subscripts. This is a bounded observation about the older-edition
errata, not an exhaustive errata claim. The public note
`notes/renard/appendix-a-corrections.md` concerns other Appendix A discrepancies.

The explicit equivalence families and naturality equations below are a
source-derived formulation of the displayed natural isomorphisms of Hom
sets. No additive, linear or enriched structure on the Hom sets is assumed.
Lean writes `f ≫ g` for first f and then g.

## Object principle

`Langlands.Renard.IsomorphismPrinciple.ObjectStatement.{vM,uM}` binds an
arbitrary actual category `M : Type uM` with `Category.{vM} M`, two objects
X and Y, and an actual equivalence

```text
e Z : (Z ⟶ X) ≃ (Z ⟶ Y)
```

for every object Z. The sole additional hypothesis is contravariant
naturality in Z:

```text
e Z' (g ≫ f) = g ≫ e Z f
```

for every `g : Z' ⟶ Z` and `f : Z ⟶ X`. The conclusion
`Nonempty (X ≅ Y)` asserts existence of an actual categorical isomorphism.
The equivalences already contain inverse functions and both inverse laws;
the statement therefore needs only the displayed forward naturality
equation. It does not assert that arbitrary isomorphisms from X to Y are
unique.

## Functor principle

`Langlands.Renard.IsomorphismPrinciple.FunctorStatement.{vC,vM,uC,uM}` binds
arbitrary actual categories C and M, with four independent object and
morphism universe levels, and actual functors `F G : C ⥤ M`. It binds
actual equivalences

```text
e X Z : (Z ⟶ F.obj X) ≃ (Z ⟶ G.obj X)
```

for every X in C and Z in M. Both naturality hypotheses are explicit.
Contravariant naturality in Z is

```text
e X Z' (g ≫ f) = g ≫ e X Z f
```

for all `g : Z' ⟶ Z` and `f : Z ⟶ F.obj X`. Covariant naturality in X is

```text
e X' Z (f ≫ F.map a) = e X Z f ≫ G.map a
```

for all `a : X ⟶ X'`, Z, and `f : Z ⟶ F.obj X`. Thus the supplied
equivalences respect both Hom variables, as required by display
(A.III.3.2). The conclusion `Nonempty (F ≅ G)` asserts an actual natural
isomorphism in the functor category, including naturality of its components.

Neither component assumes fullness, faithfulness, smallness, nonemptiness,
representability data or a preexisting object or functor isomorphism.
The categories and functors need no additive, finiteness or limit structure.
The Hom-family formulation leaves all four universes independent without
choosing a separate universe of sets or identifying any of the levels.

## Aggregate and remaining proof

`Langlands.Renard.IsomorphismPrinciple.IsomorphismPrincipleStatements` is
the conjunction of `ObjectStatement` and `FunctorStatement`, in that order,
with their indicated universe arguments. Each component binds every
mathematical input internally, so the aggregate is a closed Prop-valued
definition.

The imported actual Mathlib Yoneda construction is a possible reuse route
for a later proof. `CategoryTheory.Yoneda.ext` constructs an object
isomorphism from inverse Hom maps and the same precomposition equation.
For functors, the equivalences at each X give such object isomorphisms;
naturality in X must then give the naturality of their forward maps.
These observations describe an intended route, not an implemented proof.

An exact-proof successor must target the unchanged aggregate after its
independent acceptance and actual Library publication. This pair does not
supply the general Yoneda lemma, the representability assertions of A.III.2,
compatible uniqueness of representations, adjunctions, or completion of
Appendix A.III or the whole-book program.
