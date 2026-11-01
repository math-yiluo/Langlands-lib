# Renard A.III.1: universal arrows and compatible comparison

This is a statement-only unit for the definition of right and left universal
problems and the following comparison remark in David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, Appendix A.III.1, printed pp.251–252 / one-based PDF257–258.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 read these original pages directly and inspected the PDF258 image.

The current discrepancy note `notes/renard/appendix-a-corrections.md`
concerns example 4 in this subsection, constant-functor comparisons in A.IV
and abelian subcategories in A.VI. It does not change these generic
factorization definitions. The older-edition supplement registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked at PDF18–19. That bounded check provides no correction to the
generic comparison remark; it is not an exhaustive errata claim.

## Exact declarations and hypotheses

The namespace is `Langlands.Renard.UniversalArrow`. Each component is a
closed `Prop`-valued definition. It universally quantifies actual categories
`A : Type uA`, `B : Type uB`, their structures `Category.{vA} A` and
`Category.{vB} B`, an actual functor `F : A ⥤ B`, and an object `Y : B`.
The object and morphism universe levels of both categories are independent.
The only assumptions on the categories and functor are their defining laws.

1. `RightCharacterizationStatement` quantifies `X : A` and
   `i : Y ⟶ F.obj X`. It asserts that
   `∀ Z f, ∃! g : X ⟶ Z, i ≫ F.map g = f` is equivalent to
   `Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk i))`.
   Here `Z : A` and `f : Y ⟶ F.obj Z`.
2. `LeftCharacterizationStatement` quantifies `X : A` and
   `j : F.obj X ⟶ Y`. It asserts that
   `∀ Z f, ∃! g : Z ⟶ X, F.map g ≫ j = f` is equivalent to
   `Nonempty (CostructuredArrow.IsUniversal (CostructuredArrow.mk j))`.
   Here `Z : A` and `f : F.obj Z ⟶ Y`.
3. `RightComparisonStatement` takes two actual source-style right solutions
   `(X,i)` and `(X',i')`, each with the full factorization property above.
   Its conclusion is `∃! e : X ≅ X', i ≫ F.map e.hom = i'`.
4. `LeftComparisonStatement` takes two actual source-style left solutions
   `(X,j)` and `(X',j')`, each with the full left factorization property.
   Its conclusion is `∃! e : X ≅ X', F.map e.hom ≫ j' = j`.

`UniversalArrowStatements.{vA,vB,uA,uB}` is the conjunction of these four
closed propositions, in that order. Every mathematical input is bound inside
each component; there is no extra category, functor or solution parameter on
the aggregate.

## Correspondence and provenance

Renard writes composition in function order. Lean's equation
`i ≫ F.map g = f` expresses the source's `F(g) ∘ i = f`, and
`F.map g ≫ j = f` expresses `j ∘ F(g) = f`. These are the right and left
universal properties in the original definition on printed251/PDF257.

Mathlib calls a structured arrow universal when it is initial, and a
costructured arrow universal when it is terminal. In the pinned source,
`StructuredArrow.IsUniversal` abbreviates `IsInitial` and
`CostructuredArrow.IsUniversal` abbreviates `IsTerminal`. These are types of
data. The explicit `Nonempty` wrappers make their existence propositions.
The two equivalences are internal formulations of the source definition
using these actual comma categories and their existing Mathlib constructors.
No replacement category or chosen family of factor maps is assumed.

The source comparison remark on printed252/PDF258 constructs two factor
maps by applying universality to `i` and `i'`, and uses uniqueness to show
that they are inverse. It states that the same argument applies on the
left. The comparison propositions retain compatibility with the original
arrows. Their unique object is an isomorphism satisfying that equation;
they make no assertion that all underlying isomorphisms from `X` to `X'`
are equal. In particular the forward compatibility condition is explicit
in each `∃!`. The dual comparison has the arrow direction required by
`j ∘ F(g) = f`.

These are source-derived formulations. They do not assume fullness,
faithfulness, essential surjectivity, a size restriction, limits,
representability, or an adjunction. They do not assert that an arbitrary
universal problem has a solution. The particular module-localization
construction and its categorical universal property are separate units.

## Proof boundary

This file supplies proposition definitions and no proof of them.
Independent statement acceptance and actual Library publication are required
before a separate exact-proof task can target `UniversalArrowStatements`
in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
The expected reusable Mathlib APIs include the two
`IsUniversal.existsUnique` results and the constructors and uniqueness
results for initial and terminal objects. Any eventual proof Markdown must
describe the implemented route. Other examples, functoriality, adjunctions,
representability and the remaining assertions of Appendix A stay open.
