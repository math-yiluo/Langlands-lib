# Renard A.VIII.2: the regular unital module is a small progenerator

Authors: Worker 734 (source rereading, implementation, compilation and
inspection, documentation); Worker 6 (the proposed type and body, adopted
verbatim from the objective of task `71264c9b-d96b-47f9-bc18-e4a1ab3e55b5`;
an independent draft pair, shared as that task's draft revision 1, whose
Markdown formulations were partly adopted here; and an independent private
inspection probe).

This statement unit supplies
`Langlands.Renard.RegularModuleSmallProgeneratorStatement` in module
`Langlands.CategoryTheory.Renard.RegularModuleSmallProgeneratorStatements`.
It states that the regular module of a unital ring is a small progenerator
of the ring's category of unital left modules, at an explicit coproduct
index size. It supplies no proof.

## Original source and reading boundary

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

The formalized assertion is the unnumbered remark in A.VIII.2 on printed
page 267 / PDF page 273:

> Remarque. On a bien sûr la réciproque, puisque un anneau unitaire `A` est
> un petit progénérateur de `M(A)`

It directly follows the theorem that a cocomplete abelian category with a
small progenerator `P` is naturally equivalent, through `Hom_A(P, •)`, to
the category of unital right modules over `R_P = End_A(P)`. Renard gives
the remark without proof; the surrounding text cites Pareigis [37], 4.11.
That cited source has not been read for this unit, and no proof from it is
claimed to have been checked. Only the regular-object assertion, the
reason the remark gives, is formalized here. The converse itself (that a
category equivalent to a category of unital modules admits a small
progenerator) and the equivalence theorem are not stated.

On the same page Renard defines the relevant notions for an abelian
category `A`: `X` is projective if `Hom_A(X, •)` is exact; `X` is a
generator if `Hom_A(X, •)` is faithful; a progenerator is a projective
generator; and, for `A` cocomplete, a projective object `P` is small if
`Hom_A(P, •)` preserves direct sums. Exactness of an additive functor is
defined in A.VIII.1, printed page 266 / PDF page 272, by the preservation of
the two one-sided exact sequences. Complete PDF pages 272–273 were read.

The module conventions were read on printed pages 5–7 / PDF pages 11–13.
`A−mod` denotes left `A`-modules and `mod−A` right `A`-modules (PDF 11).
Rings are not assumed unital unless explicitly stated, and modules over a
unital ring are not assumed unital a priori; for unital `A`, `M(A)` is the
full subcategory of `A−mod` whose objects are the unital modules, those on
which `1_A` acts as the identity (PDF 11, footnote 1, and PDF 12). For a ring
with idempotents, `M(A)` is the category of nondegenerate *left* modules and
`M(A)_d` that of nondegenerate right modules; a unital ring is a ring with
idempotents whose nondegenerate modules are exactly its unital modules, so
the two meanings of `M(A)` agree (PDF 13). Hence `M(A)` in the remark is the
category of unital left `A`-modules.

The supplementary author errata for the 2010 edition,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at their Appendix A entries on PDF pages 18–19. The correction
for printed page 309, line 2, replaces `X` by `P` in the smallness condition
on `Hom(P, •)`; the 2026 text already incorporates it. Those two errata
pages contain no correction to the regular-module remark; this is a bounded
observation about the consulted pages and edition. The public
`notes/renard/appendix-a-corrections.md` has no entry for this passage, and
no `notes/errata` directory is present in the inspected current Library.

## Complete statement

The declaration, with all parameters and body, is:

```lean
universe w v u

def RegularModuleSmallProgeneratorStatement (R : Type u) [Ring R]
    [HasCoproducts.{w} (ModuleCat.{max u v} R)] : Prop :=
  HomSmallProgenerator.{w} (ModuleCat.of R (ULift.{v} R))
```

It is an ordinary transparent `def` returning `Prop`. The coproduct
binder is an explicit hypothesis of the declaration, and the body passes it
to `HomSmallProgenerator`. Besides the published
`Langlands.CategoryTheory.Renard.SmallProjective`, the module imports
`Mathlib.Algebra.Category.ModuleCat.Abelian`, which supplies the abelian
structure `ModuleCat.abelian` required by `HomSmallProgenerator`, and
`Mathlib.Algebra.Module.ULift`, which supplies the lifted module
structure. No conclusion of the remark is assumed as an instance or
hypothesis, and no replacement functor or distinguished object is
introduced.

## The category and the regular object

`ModuleCat.{max u v} R` is Mathlib's category of left `R`-modules with
carriers in `Type (max u v)`. `R` is an arbitrary unital ring, possibly
noncommutative; the zero ring is allowed. There is no field, coefficient
algebra, Noetherian, nonzero-ring or finite-dimensionality hypothesis.
Mathlib's `Module` structure includes `one_smul`, so these are exactly the
unital left modules: the category is the source's `M(R)`, not the category
of arbitrary (possibly nonunital) actions of Chapter I. Nonunital source
categories remain separate.

The object is `ModuleCat.of R (ULift.{v} R)`: its carrier is `ULift.{v} R`,
the lift of `R` to `Type (max u v)`, with Mathlib's native instances
`ULift.addCommGroup` and `ULift.module'` (the latter applied to the regular
module `Semiring.toModule`). Addition is `up x + up y = up (x + y)`, and
`r` acts by left multiplication, `r • up x = up (r * x)`; in particular the
unit acts as the identity. This is the concrete regular module, not an
arbitrary object equipped with assumed properties, and no new construction
is made. The lift is needed because objects of `ModuleCat.{max u v} R`
have carriers in `Type (max u v)`, while `R` itself lies in `Type u`.

## Left modules and the right-module specialization

Renard's equivalence theorem produces *right* modules over `End_A(P)`,
while the remark concerns `M(A)`, which by the conventions above consists
of unital *left* modules. The Lean statement follows the remark's left
convention. The right-module form is the specialization `R := Rᵐᵒᵖ`:
`ModuleCat Rᵐᵒᵖ` is the category of left `Rᵐᵒᵖ`-modules, that is, of right
`R`-modules. The carrier of its regular object is `ULift.{v} Rᵐᵒᵖ`, and
`unop` identifies `Rᵐᵒᵖ` with `R` additively. Under this identification
`op a • up (op x) = up (op (x * a))`, so `op a` acts as right
multiplication by `a`. This specialization is pure substitution in the
declaration; no category equivalence, Morita equivalence or identification
of `End(R)` with `Rᵐᵒᵖ` is stated or assumed.

## Meaning of the imported predicates

All are imported unchanged from the published
`Langlands.CategoryTheory.Renard.SmallProjective`,
`Langlands.CategoryTheory.Renard.HomObjectProperties` and
`Langlands.CategoryTheory.Renard.HomFunctors`. Write `P` for the regular
object.

`HomSmallProgenerator.{w} P` is `HomSmallProjective.{w} P ∧ HomGenerator P`,
and `HomSmallProjective.{w} P` is `HomProjective P ∧ HomPreservesCoproducts.{w} P`.
Each condition concerns the actual functor
`Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P`, Renard's
`Hom(P, •)` into abelian groups. It takes `X` to the integer module with
carrier `P ⟶ X` (morphisms of `ModuleCat`, which wrap `R`-linear maps), with
the canonical integer action of that additive group, and sends `g : X ⟶ Y`
to postcomposition `f ↦ f ≫ g`. Here its target is `ModuleCat.{max u v} ℤ`.

- `HomProjective P` is `SequenceExact` of this functor (from
  `Langlands.CategoryTheory.RenardExactFunctor`), the conjunction of both
  one-sided conditions of A.VIII.1: every exact `0 ⟶ X ⟶ Y ⟶ Z` (an exact
  short complex with monomorphic first map) goes to an exact sequence with
  monomorphic first map, and every exact `X ⟶ Y ⟶ Z ⟶ 0` (exact with
  epimorphic second map) goes to an exact sequence with epimorphic second
  map. The inputs are not restricted to short exact sequences.
- `HomPreservesCoproducts.{w} P` says that for every `I : Type w` the
  functor preserves all colimits of shape `Discrete I`, that is, every
  coproduct cocone of every `I`-indexed family of modules, including empty
  families. Preservation is Mathlib's `PreservesColimitsOfShape`: the
  image of each colimit cocone is a colimit cocone. It tests the mapped
  cocones directly by their universal property, so it needs no coproduct
  existence in the target as an extra hypothesis.
- `HomGenerator P` is faithfulness of this functor, Mathlib's
  `Functor.Faithful`: injectivity of its action on every Hom type, for all
  pairs of modules.

## Universes and coproduct size

The ring universe `u`, the extra carrier universe `v` and the coproduct
index universe `w` are independent. Carriers and Hom types live in
`Type (max u v)`; the object type `ModuleCat.{max u v} R` lives in the
successor universe `max u v + 1`. Specializing `v` cannot drop the regular
module, because the carrier universe always contains `ULift.{v} R`.

The binder `[HasCoproducts.{w} (ModuleCat.{max u v} R)]` is retained in the
full declaration. It is required by `HomSmallProgenerator`: it is the
coproduct-existence form, at the chosen size, of the source's
cocompleteness hypothesis in the definition of smallness. At the carrier size
`w = max u v` Mathlib supplies it: native module colimits are built in
`Mathlib/Algebra/Category/ModuleCat/Colimits.lean` from colimits of abelian
groups, and private `inferInstance` checks found
`HasColimitsOfSize.{max u v, max u v}` and `HasCoproducts.{max u v}` for
`ModuleCat.{max u v} R`, and also `HasCoproducts` at the sizes `0`, `u` and
`v`. No automatic coproduct existence is claimed at any other, unrelated
size `w`. A private check found no instance at one larger size,
`HasCoproducts.{3} (ModuleCat.{2} (ULift.{2} ℤ))`; this is a single
observation, not a general claim. Different index sizes give different
instances of the proposition, and no comparison between them is proved
here.

Other prepared Mathlib files, `Mathlib/Algebra/Category/ModuleCat/Ulift.lean`
(lifted modules and the lift functor) and
`Mathlib/Algebra/Category/ModuleCat/Projective.lean` (bridges between module
and categorical projectivity), are relevant to a later proof. They are not
used by this statement and do not by themselves prove the source Hom
predicates.

Freyd's argument, recorded in the published Markdown of
`Langlands.CategoryTheory.Renard.IndexedSubobjectSums` (paragraph "Collapse
under the global hypothesis"), uses a coproduct indexed by the type
`Σ A B, (A ⟶ B)` of all morphisms of the category, and shows that in an
abelian category such coproducts force every object to be zero. For
`ModuleCat.{max u v} R` that type lies in `Type (max u v + 1)`, so the
argument does not apply to the size-`max u v` instance above. Informally,
the same argument shows that at `w = max u v + 1` the binder can be
supplied only when every module is zero, that is, only for the zero ring;
this was not formalized. These are remarks about meaningful choices of `w`;
the statement does not depend on them.

## Verification and remaining obligations

Development compilation and full declaration inspection were performed in
approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with prepared
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`. The workspace
check `b4df8c9a-221d-432f-b0b0-e663799e26d3` reports 0 errors and 0 warnings,
and its inspection reports a `definition` with level parameters `w, v, u`,
returning `Prop`, whose axioms are only `propext`, `Classical.choice` and
`Quot.sound`.

A private probe module compiled with the statement (latest diagnostic
`3060c300-fc86-4ea0-afbc-e63117245a68`, earlier
`addc2947-5372-4556-a5b0-c448968a339b`, each with 0 errors and 0 warnings).
It checked by `rfl` that the complete unapplied declaration is

```lean
fun (R : Type u) (_ : Ring R) (inst : HasCoproducts.{w} (ModuleCat.{max u v} R)) =>
  @HomSmallProgenerator.{w, max u v, max u v + 1} (ModuleCat.{max u v} R) _ _ inst
    (ModuleCat.of R (ULift.{v} R))
```

so the coproduct binder is the instance used by the body. It checked by
`Iff.rfl` the unfolding to `HomProjective`, preservation of `Discrete I`
colimits for every `I : Type w`, and `HomGenerator`; by `rfl` the carrier
`ULift.{v} R`, the lifted addition and left action, the right action
`op a • up (op x) = up (op (x * a))` over `Rᵐᵒᵖ`, and the Hom carrier
`P ⟶ X`; by `one_smul` that the unit acts as the identity; by
`inferInstance` the Hom universe `Category.{max u v}` and the coproduct
instances listed above; and that the actual Hom functor has type
`ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} ℤ`. `#print` with universes
showed the instances `ModuleCat.abelian`, `ULift.addCommGroup` and
`ULift.module'`. The full unapplied type, with the coproduct binder, was
checked at the triples `(w, v, u) = (0, 1, 2), (2, 0, 1), (1, 2, 0)`.
The declaration elaborated for `ℤ`, the zero ring `PUnit`,
the noncommutative ring `Matrix (Fin 2) (Fin 2) ℚ` and `ℤᵐᵒᵖ` at universes
`{0, 0, 0}`; for `ℤ` at `{2, 2, 0}` and `{0, 1, 0}`; for `ULift.{2} ℤ` at
`{1, 1, 2}`; for general `R` at `{max u v, v, u}`; and at `{5, 1, 0}` for `ℤ`
under an explicitly assumed `HasCoproducts.{5}` hypothesis. Worker 6's
independent private probe (diagnostic
`ee5ff0ea-bc1f-4ae2-b486-3d5e8d54ba3c`) made comparable checks of the
unapplied type and body, the universe triples above and `{0, 0, 0}`, the
carrier and action, the opposite-ring order and the coproduct instance at
`max u v`. These checks establish elaboration, the proposition kind and
the actual object; they do not prove the remark or establish independent
semantic acceptance.

The proof is a separate exact-target successor after independent statement
publication. A route through evaluation at the lifted unit has not been
implemented or checked. The following remain separate obligations: the
small-progenerator equivalence with right `End(P)`-modules, nonunital source
module categories, the finite-support and finite-type assertions of A.VIII.2
(tasks `f27c1b29-df22-46eb-ae83-ee1e258cba79` and
`372132dd-d49a-4c66-a628-f335dadd820d`) and their proofs. Presentations by
copies of a small progenerator already have the public proof
`Langlands.Renard.generatorPresentation`, which this unit does not
duplicate. No proof sketch, imported theorem or circular assumption is
supplied in this statement pair.
