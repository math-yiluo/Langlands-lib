# Renard A.II.2: the equivalence criterion

This statement unit supplies
`Langlands.Renard.EquivalenceCriterionStatement`. It expresses the
sufficient criterion in the unnumbered theorem at the end of A.II.2 using
an actual quasi-inverse. It contains no proof of that proposition.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

The implemented passage is A.II.2, printed page 251 / PDF257: the
definition of equivalence, the full and faithful definitions, and the
final unnumbered theorem. A.II.1 on printed page 250 / PDF256 defines
natural transformations and natural isomorphisms. Those two original
pages were read, and PDF257 was also inspected visually. The composition
convention was checked at A.I.1, printed page 247 / PDF253.

The theorem says that a fully faithful functor is an equivalence if every
target object is isomorphic to an object in its image. The book cites
its references [28], Theorem 1.13, and [25], Theorem 2.3.5, without
giving a proof here. These are the book's provenance references; this
unit relies on the read Renard passage for its statement and claims no
independent reading of those references.

## Typed correction to the definition

For `F : C ⥤ D` and `G : D ⥤ C`, `F ⋙ G` is an endofunctor of `C`,
and `G ⋙ F` is an endofunctor of `D`. Thus the correctly typed
quasi-inverse condition is

```text
F ⋙ G ≅ 𝟭 C,      G ⋙ F ≅ 𝟭 D.
```

The boxed definition on PDF257 exchanges the two identity categories
when using the conventional composition notation `FG` and `GF`.
The immediately preceding strict-inverse discussion correctly places
`FG` on the target category and `GF` on the source category. A.I.1
likewise places `gf` on the source of `f`. This identifies a type error
in the boxed subscripts, rather than a different composition convention.
Lean's `⋙` writes the functors in application order, so the displayed
Lean conditions above implement the intended definition.

The supplementary registered source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked at PDF18–19 for its appendix corrections. Those pages
contain no correction of this A.II definition. This is a bounded check
of the older errata, which do not replace the 2026 reference.

## Exact statement and conventions

The categories have four independent universes:
`C : Type u₁` with `Category.{v₁} C`, and `D : Type u₂` with
`Category.{v₂} D`. The target quantifies every `F : C ⥤ D` and assumes:

1. Every map `Hom(X,Y) → Hom(F(X),F(Y))` is surjective.
2. Every such map is injective.
3. Every `Y : D` has some `X : C` and an isomorphism `F.obj X ≅ Y`.

The conclusion is the existence of a functor `G : D ⥤ C` together with
the existence of each of the two natural isomorphisms displayed above.
`Nonempty` turns the actual isomorphism types into propositions. It
does not substitute pointwise isomorphisms for natural isomorphisms:
the outer isomorphisms live in the actual functor categories.
No triangle identity is assumed in the conclusion, just as none is
required by the source's quasi-inverse definition.

There is no nonemptiness, smallness, abelian, additive, finiteness or
common-universe hypothesis. Empty categories are included. The theorem
is a sufficiency statement; a converse or an iff would be additional
derived content.

## Reuse and remaining work

The imported `Mathlib.CategoryTheory.Equivalence` supplies the actual
functors, natural transformations and functor-category isomorphisms.
At the pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`,
`Functor.Full.map_surjective` and `Functor.Faithful.map_injective`
express precisely the first two hypotheses.
`Functor.EssSurj.mem_essImage` and `Functor.essImage` express the third.

Mathlib's `Functor.IsEquivalence` is defined by full faithfulness and
essential surjectivity. Therefore using that class alone as the
conclusion would omit the explicit source-to-quasi-inverse bridge.
`Functor.asEquivalence` constructs an actual equivalence from those
properties, and its `unitIso.symm` and `counitIso` have the required
types. This is a reuse route for a separate proof of the published
statement, not a proof exported by this unit.

The vector-space skeleton example on PDF257, the general representative
subcategory discussion, and any additional A.I–A.II source bridges remain
separate whole-book obligations. Acceptance of this statement does not
close A.II or the parent program.

Author: Worker 709.
