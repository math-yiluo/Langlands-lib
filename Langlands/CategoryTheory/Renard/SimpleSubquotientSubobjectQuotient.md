# Simple subquotients of a subobject and quotient

Author: Worker 695.

This module proves `Langlands.Renard.simpleSubquotientSubobjectQuotient`,
whose entire type is

```lean
theorem simpleSubquotientSubobjectQuotient
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSubquotientSubobjectQuotientStatement.{w} C
```

The constant has independent universe parameters `w`, `v` and `u`.
The unchanged published target unfolds to

```lean
IsSourceGrothendieck.{w} C → SourceAB6 C →
  ∀ (X : C) (P : Subobject X),
    simpleSubquotientClasses X =
      simpleSubquotientClasses (P : C) ∪
        simpleSubquotientClasses (cokernel P.arrow)
```

The proof imports the published statement module
`Langlands.CategoryTheory.Renard.SimpleSubquotientIdentitiesStatements`.
Its Lean/Markdown pair and its entire imported project closure are
unchanged.

## Sources and scope

The result is clause (i) of the unnumbered Lemma in David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, Appendix A.VI.3, printed264/PDF270. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`; retained original:
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`;
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF269–270 were read completely and the rendered Lemma on PDF270 was
checked visually. The source calls clause (i) clear; the categorical
argument below supplies the implemented details.

The public note `notes/renard/appendix-a-corrections.md` concerns other
passages. No dedicated erratum for this Lemma was present in the
inspected project material. The supplementary registered
`renard-2010-corrections-complements`, retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF18–19. Its chain correction concerns the preceding
simple-quotient Proposition. No entry in that inspected range corrects
this Lemma. This is a bounded comparison with a different edition's
supplementary errata.

The internal argument works in every abelian category. The exported
exact target retains the source Grothendieck and canonical AB6
antecedents internally, although this clause does not use them.
Family universe `w`, Hom universe `v` and object universe `u` remain
independent. There is no finite-length, concrete-category, module,
smallness, `WellPowered`, `LocallySmall`, generator or separator
hypothesis. Every `X` and every subobject `P`, including zero and top,
are allowed.

## Actual presentations and transports

The four helper theorems are internal derived results of this
formalization, rather than separately quoted results from Renard.
They all have only `[Category.{v} C] [Abelian C]` as ambient hypotheses.

`objectClass_mem_simpleSubquotientClasses_of_mono_epi` takes an actual
monomorphism `m : M ⟶ X`, an actual epimorphism `p : M ⟶ S` and
`Simple S`. It constructs

```lean
A := Subobject.mk (kernel.ι p ≫ m)
B := Subobject.mk m
```

with `A ≤ B` witnessed by `kernel.ι p`. The chosen representative
isomorphisms `Subobject.underlyingIso` identify the actual
`Subobject.ofLE A B h` with `kernel.ι p`. Their commuting square gives
an isomorphism of actual cokernels via `cokernel.mapIso`.
`Abelian.factorThruCoimage p` is an isomorphism because `p` is epi,
so this cokernel is isomorphic to `S`. `Simple.of_iso` and
`objectClass_eq_iff` give exactly the two witnesses required by the
published definition of `simpleSubquotientClasses X`. No alternative
definition of subquotient classes is introduced.

`simpleSubquotientClasses_subset_of_mono` composes a presenting
subobject inclusion with a given monomorphism. Its epi presentation
is the original actual cokernel projection.

`simpleSubquotientClasses_subset_of_epi` lifts a presentation through
an epimorphism `p : X ⟶ Y`. For a presenting subobject `B` of `Y`,
the actual pullback of `B.arrow` and `p` has a monomorphism to `X`
and an epimorphism to `(B : C)`. Composing the latter with the
original cokernel projection and applying the first helper produces
the required actual subobject interval of `X`.

## Forward inclusion and final equality

`simpleSubquotientClasses_subset_union` starts with an actual
simple quotient `S := cokernel (Subobject.ofLE A B h)` of a subobject
`B` of `X`; write `p : (B : C) ⟶ S` for its cokernel projection.
Pull back `B.arrow` and `P.arrow`. Write the projections as
`t : E ⟶ (B : C)` and `l : E ⟶ (P : C)`.

If `t ≫ p` is nonzero, `epi_of_nonzero_to_simple` makes it an
epimorphism. Since `l` is mono, the first helper realizes the class
of `S` as a simple subquotient of `(P : C)`.

If `t ≫ p = 0`, the actual cokernel universal property gives
`d : cokernel t ⟶ S`. It is epi because
`cokernel.π t ≫ d = p` and `p` is epi. The actual pullback square
induces

```lean
j := cokernel.map t P.arrow l B.arrow pullback.condition
```

from `cokernel t` to `cokernel P.arrow`.
`Abelian.mono_cokernel_map_of_isPullback` proves that this very map
is mono. Applying the first helper to `j` and `d` realizes the class
of `S` as a simple subquotient of the ambient quotient.

The final theorem introduces the two source antecedents and combines
this forward inclusion with the union of the mono transport along
`P.arrow` and the epi transport along `cokernel.π P.arrow`.
Set antisymmetry gives the exact required equality.

The Mathlib APIs used here were checked against their sources at
commit `5ed2965256430c3649e86755f9576b54eca72435`, principally
`CategoryTheory/Subobject/Basic`, `CategoryTheory/Limits/Shapes/Kernels`,
`CategoryTheory/Abelian/Basic`, `CategoryTheory/Abelian/CommSq` and
`CategoryTheory/Simple`. The Lean service checks the implemented
constructions. The proof uses no simple-quotient existence theorem,
numerical length or finite-length argument. Clauses (ii), (iii)
and the aggregate statement remain separate obligations.
