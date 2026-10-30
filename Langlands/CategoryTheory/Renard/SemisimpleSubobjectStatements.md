# Renard A.VII: subobjects of semisimple objects

Module: `Langlands.CategoryTheory.Renard.SemisimpleSubobjectStatements`.
The single declaration `Langlands.Renard.SemisimpleSubobjectStatement` is a
definition returning `Prop`. It states the unnumbered corollary after the
semisimplicity lemma of A.VII. This unit supplies no proof of the corollary.

## Original and conventions

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The corollary and its proof are on printed265/PDF271, immediately after the
unnumbered A.VII lemma:

> **Corollaire.** Un sous-objet d'un objet semi-simple est semi-simple.

Worker 6 read PDF269–271 in full and visually inspected PDF271. Worker 1073
independently rechecked the file's SHA256 and reread the extracted text of
PDF269–271 before submission.

The corollary itself names no hypotheses. It directly follows the lemma,
which assumes "une catégorie abélienne vérifiant les hypothèses de la section
précédente", and "semi-simple" refers to the equivalent conditions of that
lemma. The statement therefore keeps the abelian category and those
hypotheses. On printed263/PDF269, source Grothendieck means arbitrary
direct sums (AB4*) and the AB5 directed-intersection law, without a
generator. Renard's AB6 means that every object is a sum of finite-type
subobjects; the footnote says this is local finite type, not Grothendieck's
Tohoku AB6. The imported `IsSourceGrothendieck` (module
`Langlands.CategoryTheory.RenardGrothendieckAxioms`) and `SourceAB6` (module
`Langlands.CategoryTheory.Renard.LocallyFiniteType`) preserve these
conventions. A subobject is an equivalence class of monomorphisms (A.I.2,
printed248/PDF254).

The supplementary 2010-edition errata,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at PDF18–19. Those pages contain the nearby chain correction for
the preceding simple-quotient proposition (2010 p.305), already incorporated
in 2026, and no correction to this corollary. The other mention of A.VII in
that list, on PDF6 (also read), uses lemma A.VII as a tool and does not
correct it. This is a limited observation about a different edition, not an
exhaustive absence claim. The published
`notes/renard/appendix-a-corrections.md` documents other passages.

## Exact proposition

The declaration has universe parameters `r, v, u` in this order: the
source-family universe `r`, the Hom universe `v` and the object universe
`u`, all independent. It has outer parameters
`(C : Type u) [Category.{v} C] [Abelian C]` and body

```lean
IsSourceGrothendieck.{r} C → SourceAB6 C →
  ∀ (X : C) [Small.{r} (Subobject X)],
    IsSemisimpleObject X →
      ∀ (Y : C) (j : Y ⟶ X) [Mono j], IsSemisimpleObject Y
```

Both occurrences of `IsSemisimpleObject` use the unchanged public predicate
from `Langlands.CategoryTheory.RenardSemisimplicity`. It is the existing
alias `IsCompletelyReducible.{max u v}`: there is a family of simple objects
indexed by a type in `Type (max u v)` whose actual coproduct cofan has the
specified object as its vertex. It allows the empty family and is invariant
under isomorphism by the published laws `IsSemisimpleObject.of_isZero` and
`IsSemisimpleObject.of_iso`. No equivalence with a different
semisimplicity condition is assumed here.

The arbitrary monomorphism `j : Y ⟶ X` represents a subobject of `X`,
including every isomorphic representative. Taking
`Y = (P : C)` and `j = P.arrow` covers every actual `P : Subobject X`.
Conversely, `Subobject.mk j` is the categorical subobject represented by
any such monomorphism. There is no chosen complement, split-monomorphism
assumption, finite-length restriction, nonzero restriction or concrete
module hypothesis in the proposition. The zero subobject remains covered.

## Source-size convention

The source treats its families as set-indexed without distinguishing
universe levels. In this formulation `IsSourceGrothendieck.{r} C` supplies
coproducts and the directed-intersection law at size `r`. The explicit
`Small.{r} (Subobject X)` presupposition lets the source proof's families
of actual subobjects be reindexed at that size. It does not equate `r`,
`v` and `u`, and at `r = max u v` it is automatic.

No additional smallness premise at `Y` is needed. Composition with the
monomorphism `j` gives an injection
`(Subobject.map j).obj : Subobject Y → Subobject X`, proved injective by
Mathlib's `Subobject.map_obj_injective j`. Thus
`small_of_injective (Subobject.map_obj_injective j)` transfers the displayed
ambient size bound to `Subobject Y`. This is an intrinsic size observation,
not the semisimplicity conclusion. It permits using the separate A.VII
equivalence at both objects in a future proof.

There is no global `HasCoproducts.{max u v} C`, category-wide smallness,
generator, finite-dimensionality, Noetherianity or asserted complement
condition. The source-size comparison for the existing semisimple alias
belongs to the separate semisimplicity-equivalence proof.

## Proof boundary

The source proof takes an arbitrary subobject `E′` of a subobject `E` of the
semisimple object `ℰ` (here `X`), chooses a complement `ℱ` of `E′` in `ℰ`,
and sets `F = ℱ ∩ E`. The resulting two subobjects of `E`
give its binary coproduct decomposition `E = E′ ⊕ F`, which is condition
(iii) of the lemma at `E`. The lemma's equivalence then makes `E`
semisimple. The printed proof calls the ambient complement a "sous-module";
in the abelian setting this reads as a subobject.

This paragraph records the source route, not an implemented proof.
The separate semisimplicity-equivalence target, its proof, the actual
complement/intersection transport and the corollary proof retain their
own publication requirements. This statement imports only public
definitions and does not depend on an unpublished equivalence statement.
Module and representation adapters, support decompositions and the rest of
the whole-book program remain separate.

## Checks and authorship

Development checks in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the module with no errors or
warnings, reported `statement_returns_prop: true`, level parameters
`r, v, u` and only `propext`, `Classical.choice` and `Quot.sound`. A private
probe printed the complete unapplied body, checked it by `Iff.rfl` at
independent universes and at the separated instantiations `{0, 1, 2}` and
`{2, 0, 1}`, and proved the inherited `Small.{r} (Subobject Y)` instance
above. These checks are not acceptance or publication.

Worker 6 authored the initial statement pair. Worker 1073 adopted it,
independently reread the original and errata, rechecked the declaration and
revised this Markdown.
