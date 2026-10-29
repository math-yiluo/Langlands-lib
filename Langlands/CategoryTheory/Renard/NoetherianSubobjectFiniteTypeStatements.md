# Renard A.I.3: Noetherianity and finite type of all subobjects

This statement unit gives the internal formal target for the explicit
two-direction assertion in David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, Appendix A.I.3,
printed page 249 / PDF page 255. It imports the unchanged public
`Langlands.CategoryTheory.RenardFiniteType` pair and introduces only
`Langlands.Renard.NoetherianSubobjectFiniteTypeStatement`. It contains no
proof of the equivalence.

The registered governing source is
`renard-2026-representations-groupes-reductifs-padiques`, retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The complete text of PDF pages 254–255 was read, and both rendered pages,
including the equivalence paragraph on PDF page 255, were visually
inspected. The imported Lean/Markdown pair supplies the definition
conventions. The public note `notes/renard/appendix-a-corrections.md`
records three other Appendix A discrepancies and none for this passage. No
dedicated Renard 2026 errata note was found among the published notes.

The supplementary registered 2010-edition errata,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
retained at
`/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`,
was read on PDF pages 17–19. Its entries jump from page 282 to the
Appendix A entries starting at page 294, and none concerns Noetherian or
finite-type objects or this equivalence. This is a limited reading claim.
It neither audits the whole errata document nor attributes the imported
wording repairs to the author.

## Exact proposition and source correspondence

The complete declaration is:

```lean
universe u v

def NoetherianSubobjectFiniteTypeStatement (C : Type u) [Category.{v} C] : Prop :=
  HasAllSubobjectUnions C →
    ∀ X : C, Langlands.Renard.IsNoetherianObject X ↔
      ∀ P : CategoryTheory.Subobject X, Langlands.Renard.IsFiniteTypeObject (P : C)
```

The binder `∀ X : C` scopes over the whole equivalence: for every object
`X`, source Noetherianity of `X` is equivalent to finite type of every
subobject of `X`.

On PDF page 254, immediately before defining finite type, Renard writes
"On suppose ici que la catégorie 𝒞 admet des unions quelconques". By the
convention of A.I.2, this means that for every object and every family of
its subobjects the union exists. The proposition retains this
category-wide condition as the explicit antecedent `HasAllSubobjectUnions C`.
It is part of the proposition's body; there is no ambient union-existence
typeclass or instance. The antecedent keeps the source's category-wide
form. The proposition makes no claim about whether a weaker, local
hypothesis would suffice.

On PDF page 255 the source first asserts that a subobject of a Noetherian
object is of finite type ("Il est clair d'après les définitions qu'un
sous-objet d'un objet noethérien est de type fini"). It then asserts the
converse: if every subobject of `X` is of finite type, then `X` is
Noetherian. It argues both directions. The displayed equivalence combines
those two assertions without strengthening either. The equivalence is
explicit source content, while this particular proposition declaration
is its internal formal target.

The right side quantifies over all of `Subobject X`, including the top
subobject, and applies finite type to each underlying object `(P : C)`.
This coercion elaborates to `Subobject.underlying.obj P`, the domain of the
representing monomorphism that Mathlib chooses for the subobject class.
This is the existing categorical implementation of the source's convention
in A.I.2 that one calls the domain of a representing monomorphism a
subobject. Different representatives are isomorphic. The statement does
not supply a separate isomorphism-invariance proof for finite type.

The object universe `u` and Hom universe `v` remain independent. The
complete unapplied type is `(C : Type u) → [Category.{v, u} C] → Prop`, so
`C` and its category instance are the only parameters. No abelian
structure, zero object, `WellPowered`, `LocallySmall`, Grothendieck
condition, concreteness, module structure, finite-dimensionality or
identification of universes is imposed. No Noetherianity, finite type or
comparison theorem appears as a premise.

## Imported conventions

All orders and unions are those of the actual categorical subobject
types, ordered by factorization of the inclusion arrows.
`HasAllSubobjectUnions C` says that every subset of every such type,
including the empty subset, has a least upper bound. It chooses no new
lattice operation. `Langlands.Renard.IsNoetherianObject X` says that every
nonempty subset of `Subobject X` has a maximal element. That element
belongs to the subset but need not be its greatest element.
`Langlands.Renard.IsFiniteTypeObject Y` asserts existence of all subobject
unions for `Y`. It also says that no nonempty chain of subobjects of `Y`,
each different from top, has top as its least upper bound.

The imported Markdown explains the repairs it makes to the source
wording, all retained unchanged here:

- the maximal element is the selected subobject rather than `X`;
- chains in the maximality and finite-type conditions are nonempty;
- properness means that the subobject class differs from top, not that
  its domain is abstractly nonisomorphic to the ambient object;
- the cover in the separate finite-cover paragraph has union `X`.

These are internal mathematical diagnoses, not author-issued errata. The
nonempty-chain repair also matters here. Without it, the source's forward
direction would fail for a Noetherian object whose subobject order has a
single element, since there the union of the empty chain is top. The
current target uses the published predicates as they stand and assumes no
characterization theorem.

## Proof boundary

The source's forward argument takes a chain of proper subobjects of a
subobject `Y` of `X`, regards it inside the subobjects of `X`, and takes a
maximal member. Since the chain is totally ordered, that member is its
greatest member and therefore a proper union. For the converse, the
source takes an increasing sequence `B_i` with union `B`. It uses finite
type of `B` to cover `B` by finitely many `B_i`, and concludes that the
sequence stabilizes. That covering step uses the separate compactness
characterization stated just before. These are descriptions of the source
proof, not implemented Lean proofs.

For a later proof, the prepared Mathlib declaration
`CategoryTheory.Subobject.subobjectOrderIso` gives an order isomorphism
`Subobject (Y : C) ≃o Set.Iic Y` for `Y : Subobject X`. Its implementation in
`Mathlib/CategoryTheory/Subobject/Lattice.lean`, at commit
`5ed2965256430c3649e86755f9576b54eca72435`, was read. It needs only the
category instance, with no abelian, pullback, well-poweredness or
smallness assumption. It is one possible route for transporting chains and
least upper bounds. Nothing here claims that the equivalence has been
proved.

The source's general Noetherian criteria, the chain/finite-subcover
comparison, the compact-element comparison, actual `ModuleCat` examples and
Noetherian-category examples remain separate obligations. Neither those
statement families nor their conclusions are imported or used as
hypotheses. This unit contains a single Prop-valued definition, with no
new axioms or proof holes. A separate proof task for this exact target
can begin only after independent statement acceptance, publication and
admission to the Library.

## Provenance and development checks

Worker 6 read the source passages, designed the statement and wrote the
Lean file and the first version of this Markdown, shared as draft
revision 1 of task `c8788c52-6271-4f3d-b61b-0333cc8d661b`. Worker 951
independently reread PDF pages 254–255 and their rendered images, the 2010
errata pages, the imported pair and the Mathlib order isomorphism. Worker
951 then rechecked the declaration and revised this Markdown. The Lean
file is unchanged from the draft.

A development check in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
compiled the module with no diagnostics. It reported
`statement_returns_prop: true`, universe parameters `u` and `v`, and only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`. A
private check printed the complete unapplied type and body shown above. It
accepted instantiations with distinct object and Hom universe levels, and
confirmed by `Iff.rfl` that the body unfolds to the expected formula with
all imported predicate bodies expanded. These development checks
establish no independent acceptance or publication.
