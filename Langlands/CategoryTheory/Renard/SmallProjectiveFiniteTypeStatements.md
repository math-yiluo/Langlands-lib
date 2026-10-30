# Renard A.VIII.2: small projectives and projective finite-type objects

Authors: Worker 6 (statement design, implementation and documentation);
Worker 937 (independent source rereading, compilation and inspection, and the
size-degeneracy and module-instance explanations).

This statement unit supplies
`Langlands.Renard.SmallProjectiveFiniteTypeStatement` in module
`Langlands.CategoryTheory.Renard.SmallProjectiveFiniteTypeStatements`.
It records the comparison in an arbitrary abelian category with Renard's
Grothendieck hypothesis and explicit sizes. It supplies no proof.

## Original source and reading boundary

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Complete PDF pages 272–273 (printed 266–267) were read for A.VIII.1–2.
The comparison is the unnumbered assertion in A.VIII.2 on printed page 267 /
PDF page 273: in a Grothendieck category an object is small projective if
and only if it is projective of finite type. Renard cites Pareigis [37],
4.11, Lemma 1. That cited source has not been read for this unit, and no
proof from it is claimed to have been checked.

The definitions of source Grothendieck, AB4* and AB5 were reread on printed
page 263 / PDF page 269, and those of subobject unions and finite type on
printed pages 248–249 / PDF pages 254–255. These complete pages establish
the meanings of the public predicates used here.

The supplementary author errata for the 2010 edition,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at their Appendix A entries on PDF pages 18–19. The correction
for printed page 309, line 2, replaces `X` by `P` in the smallness condition
on `Hom(P, •)`. The 2026 text already incorporates it. Those two errata
pages contain no correction to the finite-type comparison; this is a
bounded observation about the consulted pages and edition. The public
`notes/renard/appendix-a-corrections.md` concerns other Appendix A passages.
No `notes/errata` directory is present in the inspected current Library.

## Complete statement

The declaration, with all parameters and body, is:

```lean
universe w v u

def SmallProjectiveFiniteTypeStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ hG : IsSourceGrothendieck.{w} C,
    letI : HasCoproducts.{w} C := hG.1
    ∀ (P : C) [Small.{w} (Subobject P)],
      HomSmallProjective.{w} P ↔ HomProjective P ∧ IsFiniteTypeObject P
```

The declaration is an ordinary transparent `def` returning `Prop`.
`hG` is a hypothesis of the proposition. Its first conjunct supplies the
local coproduct-existence instance required by `HomSmallProjective`.
No separate coproduct-existence or preservation hypothesis is added.
The conclusion includes projectivity on both sides through the unchanged
public small-projective definition and the explicit right-hand conjunction.

## Meaning of the imported predicates

`IsSourceGrothendieck.{w} C`, from
`Langlands.CategoryTheory.RenardGrothendieckAxioms`, means source
cocompleteness at size `w` and the source AB5 distribution law: for every
nonempty directed family of subobjects indexed in `Type w`, its sum
exists, and intersection with any subobject is the sum of the
intersections. The source's cocompleteness means coproduct existence,
`HasCoproducts.{w} C`. There is no generator clause. This is the published
source convention; no comparison with Mathlib's `IsGrothendieckAbelian`
is assumed. Source AB6, the distinct local-finite-type condition on the
category, is not a hypothesis of the comparison.

`HomSmallProjective.{w} P`, from
`Langlands.CategoryTheory.Renard.SmallProjective`, is
`HomProjective P ∧ HomPreservesCoproducts.{w} P`.
`HomProjective P` means source sequence exactness of the actual functor
`Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P`.
This functor takes `X` to the integer module with carrier `P ⟶ X` and
sends a morphism `g : X ⟶ Y` to postcomposition `f ↦ f ≫ g`.
Its target is `ModuleCat.{v} ℤ`, and its integer action is the canonical
action of the additive group `P ⟶ X`. Sequence exactness
(`SequenceExact`, from `Langlands.CategoryTheory.RenardExactFunctor`) is the
conjunction of the two one-sided conditions of A.VIII.1, printed page 266 /
PDF page 272: every exact `0 ⟶ X ⟶ Y ⟶ Z` (a short complex that is exact
with a monomorphic first map) goes to an exact sequence with a monomorphic
first map, and every exact `X ⟶ Y ⟶ Z ⟶ 0` (exact with an epimorphic second
map) goes to an exact sequence with an epimorphic second map. It tests both
source one-sided exact sequences, rather than only short exact sequences.
`HomPreservesCoproducts.{w} P` says that, for every `I : Type w`, this
actual functor preserves all colimits of shape `Discrete I`. Thus it tests
all actual families of objects at that size. It does not require that the
target have coproducts of every unrelated size `w`; the mapped cocones
are tested directly by their universal property.

`IsFiniteTypeObject P`, from
`Langlands.CategoryTheory.RenardFiniteType`, means that every subset of
the actual `Subobject P` has a least upper bound and that a nonempty
chain of proper subobjects cannot have top as its least upper bound.
Properness is inequality of the subobject class with top. The existing
predicate's explicit nonempty-chain repair includes the zero object in
the finite-type convention, and its union-existence conjunct prevents
unavailable unions from making finite type vacuous. These published
conventions are reused unchanged. No finite-presentability or module
finite-generation predicate replaces them.

## Universe and source set-size convention

The coproduct index universe `w`, Hom universe `v` and object universe `u`
are independent. The comparison is instantiated at any chosen size; it
asserts no automatic promotion to other coproduct sizes.

Renard uses arbitrary set-indexed families. The public finite-type
predicate quantifies over all subsets of the actual subobject type,
whereas the source Grothendieck predicate provides sums and its AB5 law
at the explicit index size `w`. The objectwise premise
`Small.{w} (Subobject P)` discloses the set-size presupposition linking
these conventions: every subset of the full subobject type can be
reindexed in `Type w`. It does not restrict the subsets tested by finite
type, assert the comparison, or assume any finite-support conclusion.
It is a size condition, not a finiteness condition.

`Subobject P` has universe `max u v`. At `w = max u v` the displayed
objectwise smallness premise has an automatic instance (`Small` of a type
in its own universe). That instantiation is, however, degenerate for
another reason: `IsSourceGrothendieck.{max u v} C` contains
`HasCoproducts.{max u v} C`, and by Freyd's argument, recorded in the
published Markdown of `Langlands.CategoryTheory.Renard.IndexedSubobjectSums`
(paragraph "Collapse under the global hypothesis"), such coproducts make
`C` thin, so in an abelian category every object is zero. The statement at
`w = max u v` is therefore meaningful only for categories whose objects are
all zero. Keeping `w` independent is what permits nonzero applications:
for large categories with small Hom types the intended size is `w = v`.
For example, for a ring `R : Type v` and `M : ModuleCat.{v} R` the premise
`Small.{v} (Subobject M)` is an existing Mathlib instance
(`CategoryTheory.small_subobject` applied to Mathlib's
`wellPowered_moduleCat`); this was confirmed by a private `inferInstance`
check. That check concerns only the smallness premise. This unit neither
states nor proves that a module category satisfies the source Grothendieck
hypothesis.

The statement does not require global coproduct existence at `max u v`:
its only coproduct existence comes from `hG` at `w`. It asserts the
comparison at one chosen size `w` at a time.
There is no universe equality, module specialization, generator, enough
projectives, Noetherianity, finite length or finite-dimensionality premise.

## Verification and remaining obligations

Development compilation and full declaration inspection were performed in
approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with prepared
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The inspection reports a `definition` with level parameters `w, v, u`,
returning `Prop`, whose axioms are only `propext`, `Classical.choice` and
`Quot.sound`. A private probe printed the complete unapplied type and body
with universes, and checked by `rfl` that the declaration is
`fun (C : Type u) [Category.{v} C] [Abelian C] => ∀ hG P, Small.{w}
(Subobject P) → (@HomSmallProjective.{w, v, u} C _ _ hG.1 P ↔ HomProjective P
∧ IsFiniteTypeObject P)`, so the coproduct instance is exactly the first
conjunct of `hG`. It also elaborated the declaration at the unequal universe
choices `{0, 1, 3}` and `{5, 2, 1}`.
These checks establish elaboration and the proposition kind; they do not
prove the comparison or establish independent semantic acceptance.

The comparison proof remains a separate exact-target successor after
independent statement publication. The adjacent finite-subcoproduct
factorization assertion, presentations by copies of a progenerator, the
regular-module converse and the actual right-module equivalence remain
separate source obligations. No proof sketch, imported theorem or circular
assumption is supplied in this statement pair.
