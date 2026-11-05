# Source axioms for Renard's full module categories

Worker 1571. This statement unit provides six closed future theorem targets and
their conjunction in
`Langlands.Algebra.RenardFullModuleAxiomStatements`, module
`Langlands.Algebra.RenardFullModuleAxiomStatements`. Every target is a `def`
returning `Prop`. None assumes the category property it asks a future proof to
establish.

## Source correspondence

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The hash was recomputed. Printed pp.263–264 / one-based PDF269–270 were read
in full and both pages were visually inspected. The original module conventions
on printed pp.5–7 / PDF11–13 were also read.

On printed p.263 / PDF269, A.VI.2 defines source AB5 as cocompleteness and
distribution of intersection over sums of filtered increasing systems of
subobjects. Its Grothendieck convention repeats cocompleteness and has no
generator clause. A.VI.3 then separately assumes source AB6: every object is a
sum of finite-type subobjects. Footnote 1 identifies this as local finite type
and explicitly distinguishes it from Tohoku AB6. On printed p.264 / PDF270,
the opening example asserts these axioms for all left modules over an arbitrary
ring and for unital left modules over a unital ring.

The six targets specialize the published source predicates to those actual
categories. The explicit universe bounds and the separate directed-distribution
targets are foundational elaborations of that example, rather than additional
numbered assertions in the book. This unit proves no instance of either
example. Its two reflexive equivalences only expose the existing definitional
source Grothendieck reading.

The published `notes/renard/appendix-a-corrections.md` and the A.VI.3 progress
note were consulted. The former treats other passages; the latter preserves
the distinction between the full examples and the I.6 nondegenerate category.
No dedicated
`notes/errata/renard-2026-representations-groupes-reductifs-padiques.md`
was present in the workspace, project notes or pinned Library. The registered
2010-edition correction list `renard-2010-corrections-complements` was read on
PDF18–19. Its nearby correction changes the Zorn argument to use chains;
it does not address these example assertions or the source AB5/AB6 definitions.
This bounded check makes no claim about all possible later errata.

## Closed declarations and selected structures

The independent levels are coefficient universe `uA`, index universe `uI` and
carrier universe `uM`. Every declaration has type `Prop` with no term
parameters. In the following complete definitions, `NonUnitalModuleCat` denotes
`Langlands.Algebra.NonUnitalModuleCat`. Each definition quantifies over the ring
and its instance internally:

```lean
NonUnitalDirectedSubobjectDistributivityStatement.{uA, uI, uM} : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A],
    letI := NonUnitalModuleCat.abelian.{uA, uM} A
    Langlands.Renard.DirectedSubobjectSumsDistribute.{uI}
      (NonUnitalModuleCat.{uA, uM} A)

NonUnitalSourceAB5Statement.{uA, uI, uM} : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A],
    letI := NonUnitalModuleCat.abelian.{uA, max uI uM} A
    Langlands.Renard.SourceAB5.{uI}
      (NonUnitalModuleCat.{uA, max uI uM} A)

NonUnitalSourceAB6Statement.{uA, uM} : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A],
    letI := NonUnitalModuleCat.abelian.{uA, uM} A
    Langlands.Renard.SourceAB6 (NonUnitalModuleCat.{uA, uM} A)

UnitalDirectedSubobjectDistributivityStatement.{uA, uI, uM} : Prop :=
  ∀ (A : Type uA) [Ring A],
    letI : CategoryTheory.Abelian (ModuleCat.{uM} A) := ModuleCat.abelian
    Langlands.Renard.DirectedSubobjectSumsDistribute.{uI} (ModuleCat.{uM} A)

UnitalSourceAB5Statement.{uA, uI, uM} : Prop :=
  ∀ (A : Type uA) [Ring A],
    letI : CategoryTheory.Abelian (ModuleCat.{max uI uM} A) := ModuleCat.abelian
    Langlands.Renard.SourceAB5.{uI} (ModuleCat.{max uI uM} A)

UnitalSourceAB6Statement.{uA, uM} : Prop :=
  ∀ (A : Type uA) [Ring A],
    letI : CategoryTheory.Abelian (ModuleCat.{uM} A) := ModuleCat.abelian
    Langlands.Renard.SourceAB6 (ModuleCat.{uM} A)
```

`FullModuleAxiomsStatement.{uA, uI, uM} : Prop` is their right-associated
conjunction in exactly that order. The two AB6 components use only `uA,uM`;
there is no indexing parameter or chosen small cover in canonical source AB6.

The nonunital targets explicitly select the published instance
`Langlands.Algebra.NonUnitalModuleCat.abelian` from
`Langlands.Algebra.NonUnitalModuleAmbientAbelianProof`. It retains the
pointwise Hom groups and uses the integer-unitization equivalence. The unital
targets explicitly select Mathlib's standard `ModuleCat.abelian` from
`Mathlib.Algebra.Category.ModuleCat.Abelian`. No abelian structure is a
parameter of a target. The published category structures, categorical
subobjects and their existing factorization order are retained.

The complete types of
`nonUnitalSourceAB5Statement_iff_isSourceGrothendieck` and
`unitalSourceAB5Statement_iff_isSourceGrothendieck` replace `SourceAB5.{uI}`
in the corresponding closed definition above by
`Langlands.Renard.IsSourceGrothendieck.{uI}` on the same category and with the
same selected abelian instance. Both are proved by `Iff.rfl`, since the latter
predicate is defined as the former. They assume no AB5, generator or
equivalence certificate and establish no category axiom.

## Meanings and family sizes

For either selected category `C`,
`Langlands.Renard.DirectedSubobjectSumsDistribute.{uI} C` is exactly

```lean
∀ (X : C) (I : Type uI), Nonempty I →
  ∀ F : I → CategoryTheory.Subobject X, Directed (· ≤ ·) F →
    ∀ N : CategoryTheory.Subobject X, ∃ U : CategoryTheory.Subobject X,
      IsLUB (Set.range F) U ∧
        IsLUB (Set.range fun i => N ⊓ F i) (N ⊓ U)
```

Both sums must exist as actual least upper bounds. Intersection is the existing
categorical pullback intersection. This condition is stated for arbitrary
`uI` in the fixed carrier category of size `uM`. It asserts no arbitrary-size
coproducts there.

`Langlands.Renard.SourceAB5.{uI} C` is
`CategoryTheory.Limits.HasCoproducts.{uI} C` together with that directed law.
The coproduct clause includes empty index types, although the directed law
uses nonempty families. The carrier `max uI uM` accommodates the required
family size; the coefficient universe `uA` remains independent and does not
inflate that bound. This statement makes no all-size coproduct claim for a
fixed smaller carrier category. Source AB5 is not defined through Mathlib's
filtered-colimit exactness `AB5OfSize` or `IsGrothendieckAbelian`, and these
targets assert no comparison with them.

`Langlands.Renard.SourceAB6 C` is the published
`Langlands.Renard.IsLocallyFiniteTypeCategory C`: for every `X : C`,

```lean
IsLUB {P : CategoryTheory.Subobject X |
  Langlands.Renard.IsFiniteTypeObject (P : C)}
  (⊤ : CategoryTheory.Subobject X)
```

Thus top is the sum of all actual categorical finite-type subobjects.
`IsFiniteTypeObject` is the published source predicate, including existence
of subobject unions and its nonempty proper-chain condition. No replacement
finite-generation notion, sized cover, selected finite-subset construction or
extra Grothendieck hypothesis is inserted into source AB6. Its carrier stays
`uM` independently of `uA` and `uI`.

## Category scope and remaining proof gate

The nonunital category is the full original additive-action category: objects
are additive commutative groups with an associative distributive action, and
maps are additive intertwiners. If the coefficient ring has a unit, its action
need not be the identity. Zero actions on nonzero additive groups are therefore
included. The unital example is Mathlib's actual `ModuleCat A`, in which the
unit acts as the identity. Neither category has extra complex-scalar data.

No nontriviality, commutativity, finite dimension, coefficient/carrier size
comparison, idempotentedness or nondegeneracy hypothesis is added. Zero rings,
zero modules and all zero actions allowed by the selected category remain
in scope. The existing I.6 targets for `NondegenerateModuleCat` retain their
distinct category, idempotented-ring hypothesis and owners. `TopModuleCat`
and other module-category comparisons are outside this unit.

Independent acceptance and publication of this pair supplies exact proposition
targets for separate source AB5 and local-finite-type proof successors retained
by the parent program. The existing integer-unitization equivalence,
`NonUnitalModuleSubobject`, `NonUnitalModuleFinitenessProof` and
`RenardModuleFiniteType` may support those proofs. This unit does not assume
their desired category conclusions, construct covers or coproducts, or prove
any of the six example targets or their aggregate. Other Appendix A assertions
and module-category comparisons remain separate obligations.
