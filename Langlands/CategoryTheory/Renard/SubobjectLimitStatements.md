# Renard A.IV: subobject intersections and unions as limits and colimits

Author: Worker 709.

This statement unit interprets the intersection exercise in Renard A.IV.1
example 6 and its union dual in A.IV.2. The chosen category is Mathlib's
actual `Subobject X`, with its existing partial order. For a discrete family
of subobjects, a cone is limiting exactly when its vertex is a greatest
lower bound; a cocone is colimiting exactly when its vertex is a least upper
bound. These are the source definitions of intersection and union.

Module: `Langlands.CategoryTheory.Renard.SubobjectLimitStatements`.
Namespace: `Langlands.Renard.SubobjectLimit`.
All three declarations are closed `Prop`-valued definitions. This file
states the comparisons; it contains no proof of them.

## Source and provenance

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

The relevant source passages are:

- A.I.2, printed page 248 / one-based PDF254: subobjects are equivalence
  classes of monomorphisms into a fixed object, ordered by factorization.
  Intersections and unions are greatest lower bounds and least upper bounds
  in this order. The source extends the definitions to arbitrary families
  and explicitly allows their failure to exist.
- A.IV.1 example 6, printed page 257 / PDF263: the reader is asked to
  interpret a subobject intersection as a limit in an appropriate category.
- A.IV.2, printed page 257 / PDF263: subobject unions are named among the
  dual colimit examples.
- The concrete limit universal property after (A.IV.1.2), printed page 256 /
  PDF262, and its dual in A.IV.2 specify the factor-map interpretation.

PDF253–257 and PDF262–263 were read in full for the source conventions and
the exercise. The original's content hash was recomputed. The supplementary
author errata `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were also checked on PDF18–19. Those pages contain no correction to the
subobject exercise or its order-bound definitions. They refer to an older
edition; the 2026 original governs this unit. No separate source errata
note was found in the inspected published notes or project notes.

The exercise does not prescribe a particular category. Choosing the thin
category `Subobject X`, using a discrete diagram, and expressing its
universal property by `IsGLB` and `IsLUB` is the present derived
interpretation. The named closed propositions, `Nonempty` wrappers and
ordered conjunction are internal formal packaging. They are not additional
definitions or numbered claims attributed to the book.

The published note `notes/renard/appendix-a-corrections.md` explains the
general limit/colimit prose arrow errors. This unit uses actual Mathlib
cones and cocones, with the concrete source factor directions. It requires
no connectedness restriction on the index category.

## Actual subobjects and the index diagram

For `C : Type uC` with `[Category.{vC} C]` and `X : C`, Mathlib defines
`Subobject X` as the thin skeleton of `MonoOver X`, the category of
monomorphisms into `X`. Its order is the source factorization order:
`P ≤ Q` precisely when the inclusion representing `P` factors through the
one representing `Q`. Its objects therefore agree with the monomorphism
classes of A.I.2. No replacement order or lattice instance is installed.

In its canonical thin category a morphism `P ⟶ Q` records `P ≤ Q`.
Compositions express transitivity. A family `F : I → Subobject X` determines
the actual functor `Discrete.functor F : Discrete I ⥤ Subobject X`.
Both the limit and colimit in this unit are taken in that subobject
category.

The object, ambient morphism and family-index universes `uC`, `vC` and
`uI` are independent. `Subobject X` lies in `Type (max uC vC)`; there
is no assumption that it can be replaced by a type in a smaller universe.
The family is already indexed by the given `I : Type uI`. No
`WellPowered`, `LocallySmall`, complete-lattice, zero-object, additive,
abelian, completeness or cocompleteness assumption occurs.

## The two propositions

`IntersectionLimitStatement.{vC,uC,uI}` internally quantifies over every
such `C`, category instance, `X`, `I`, `F` and actual
`t : Cone (Discrete.functor F)`, and asserts

```lean
Nonempty (IsLimit t) ↔ IsGLB (Set.range F) t.pt
```

The vertex `t.pt` is itself a subobject of `X`. The cone legs record
`t.pt ≤ F i` for every `i`. A competing cone has a lower-bound vertex `P`;
its factor map `P ⟶ t.pt` expresses `P ≤ t.pt`. Existence of these
factor maps is the greatest-lower-bound condition. Uniqueness and
compatibility hold in the thin category. The proposition equates this
order condition with the actual categorical limiting property.

`UnionColimitStatement.{vC,uC,uI}` binds the same data with
`t : Cocone (Discrete.functor F)` and asserts

```lean
Nonempty (IsColimit t) ↔ IsLUB (Set.range F) t.pt
```

The cocone legs record `F i ≤ t.pt`. A competing upper-bound vertex `P`
receives the factor map `t.pt ⟶ P`, expressing `t.pt ≤ P`. This is
the least-upper-bound condition, with uniqueness and compatibility again
provided by thinness.

The `Nonempty` wrappers express existence of the data-valued
`IsLimit` and `IsColimit` witnesses inside `Prop`. No universal witness
or bound property is an input assumption. The two sides are the
conclusions being compared.

`SubobjectLimitStatements.{vC,uC,uI}` is exactly

```lean
IntersectionLimitStatement.{vC,uC,uI} ∧
  UnionColimitStatement.{vC,uC,uI}
```

All inputs are bound inside the components. Empty, finite and infinite
index types are retained. For an empty family, the right sides ask for a
greatest and a least element, respectively; no nonempty-index assumption
is inserted.

## Scope

The propositions characterize the universality of supplied cones and
cocones. They do not assert that every family has an intersection or a
union. A colimit here is a colimit in `Subobject X`; no assertion is made
that the underlying representatives form a colimit in `C`, or that a
least upper bound is an elementwise union in a category of structured
sets.

The published `Langlands.CategoryTheory.Renard.IndexedSubobjectSums`
constructs particular least upper bounds from actual coproducts and images
and proves a source A.VI.2 existence result. That construction, AB5
distributivity, general conditional abelian-category completeness, the
general cone bridge, elementary diagram shapes, inverse/direct systems and
concrete abelian-group limits remain their separate units. This unit does
not complete A.IV, Appendix A or the whole-book program.
