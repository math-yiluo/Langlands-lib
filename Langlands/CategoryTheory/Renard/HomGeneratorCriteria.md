# Renard A.VIII.2: proof of the generator comparisons and projective criterion

Author: Worker 633.

This proof unit targets the unchanged published proposition
`Langlands.Renard.HomGeneratorCriteriaStatement`, imported from
`Langlands.CategoryTheory.Renard.HomGeneratorCriteriaStatements`. It uses the
actual published integer-module Hom functors and object predicates.

## Theorems and scope

All four theorems belong to namespace `Langlands.Renard` in module
`Langlands.CategoryTheory.Renard.HomGeneratorCriteria`. Their complete
common context and signatures are:

```lean
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem homGeneratorComparison (P : C) :
  HomGeneratorComparisonStatement P

theorem homCogeneratorComparison (P : C) :
  HomCogeneratorComparisonStatement P

theorem projectiveProgeneratorCriterion (P : C) :
  ProjectiveProgeneratorCriterionStatement P

theorem homGeneratorCriteria (P : C) :
  HomGeneratorCriteriaStatement P
```

The aggregate expands to exactly

```lean
(HomGenerator P ↔ CategoryTheory.IsSeparator P) ∧
  (HomCogenerator P ↔ CategoryTheory.IsCoseparator P) ∧
  (HomProjective P →
    (HomProgenerator P ↔
      ∀ Y : C, ¬CategoryTheory.Limits.IsZero Y → ∃ f : P ⟶ Y, f ≠ 0))
```

The conjunction is right-associated in that order. The universes `v` and
`u` are independent. Projectivity is an antecedent only within the third
clause. No extra hypotheses enter any theorem. In particular, no smallness,
cocompleteness, enough-projectives or concreteness assumption is used.
The published target pair and all its imports are unchanged.

The imported `HomGenerator` and `HomCogenerator` predicates mean faithfulness
of `preadditiveCoyonedaInt P : C ⥤ ModuleCat.{v} ℤ` and
`preadditiveYonedaInt P : Cᵒᵖ ⥤ ModuleCat.{v} ℤ`, respectively, from
namespace `Langlands.CategoryTheory.Renard`. `HomProjective P` means
`SequenceExact (preadditiveCoyonedaInt P)`, and
`HomProgenerator P` means `HomProjective P ∧ HomGenerator P`.
`SequenceExact` is the published conjunction of left and right one-sided
sequence conditions; its inputs need not be short exact sequences.

## Comparison proofs

Let `U` be the faithful forgetful functor
`forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}`. The existing
`preadditiveCoyonedaInt_comp_forget₂ P` identifies
`preadditiveCoyonedaInt P ⋙ U` with
`preadditiveCoyoneda.obj (op P)`. The covariant proof rewrites the
separator side with Mathlib's
`isSeparator_iff_faithful_preadditiveCoyoneda` and then uses this identity.
It remains to compare faithfulness of `F` and `F ⋙ U`.
`Functor.Faithful.comp` supplies one direction by instance inference;
`Functor.Faithful.of_comp` supplies the other.

The contravariant proof uses
`isCoseparator_iff_faithful_preadditiveYoneda` and
`preadditiveYonedaInt_comp_forget₂ P` in exactly the same way, with source
`Cᵒᵖ`. It retains the opposite-category convention of the published functor.
These Mathlib comparison lemmas characterize the full parallel-morphism
tests. In particular, the native separator condition compares `f` and `g`
after precomposition by every `P ⟶ X`; the coseparator condition compares
them after postcomposition by every `Y ⟶ P`. Neither comparison uses the
nonzero-object criterion or a projectivity hypothesis.

## Projective criterion

For necessity, take `HomProgenerator P` and a nonzero object `Y`. If no
nonzero morphism `P ⟶ Y` exists, classical negation gives that every such
morphism is zero. `homGeneratorComparison` turns the generator component
into `IsSeparator P`. Applying its parallel-morphism test (`IsSeparator.def`)
to `𝟙 Y` and `0` gives equality: for each `f : P ⟶ Y`, both composites
are equal because `f = 0`. Mathlib's `IsZero.iff_id_eq_zero` then makes
`Y` a zero object, contradicting its nonzero hypothesis. This direction
does not use projectivity.

For sufficiency, retain the given `HomProjective P` as the first component
of `HomProgenerator P`. To obtain the generator component, apply the
published `Langlands.Renard.sequenceExactReflectsZeroFaithful` to
`F = preadditiveCoyonedaInt P`. Its source and target are abelian and its
additivity is supplied by the existing Hom construction. The sequence
exactness premise is definitionally the projectivity antecedent.

It remains to show that `F` reflects zero objects. If `F.obj Y` is zero
but `Y` is not, the assumed condition supplies `f : P ⟶ Y` with `f ≠ 0`.
Mathlib's `ModuleCat.subsingleton_of_isZero` says that the carrier of this
zero module is a subsingleton. Its carrier is definitionally `P ⟶ Y`, so
`Subsingleton.elim` gives `f = 0`, a contradiction. Classical contradiction
therefore proves `IsZero Y`. This is an argument about elements of the
actual Hom module; it does not require elements of the abstract object `Y`.
The exact-functor lemma now gives `F.Faithful`, which is `HomGenerator P`.

The aggregate pairs the three clause proofs. The proof adds no global
projectivity or faithfulness instances and no new axioms.

## Sources and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, A.VIII.2, printed page 267 /
PDF page 273, together with the preceding exact-functor lemma on printed
page 266 / PDF page 272. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 633 read both complete pages and visually checked PDF273. The
supplementary 2010 errata, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read on PDF18–19; the old p308 corrections require exactness for
preserving image factorizations and attribute sufficiency to the preceding
lemma. Both corrections are already present in the governing 2026 text.

The projective criterion is the source assertion. The comparisons with
Mathlib's native predicates are derived, and the conjunction is internal
packaging. This unit does not address the separate Hom left-exactness,
lifting, smallness, coproduct, finite-type, presentation or equivalence
obligations.

The reused Mathlib declarations are from commit
`5ed2965256430c3649e86755f9576b54eca72435`:
`CategoryTheory/Generator/Preadditive.lean`,
`CategoryTheory/Functor/FullyFaithful.lean`,
`CategoryTheory/Limits/Shapes/ZeroMorphisms.lean`, and
`Algebra/Category/ModuleCat/Basic.lean`. The sequence-exact faithfulness
lemma is imported from the published
`Langlands.CategoryTheory.Renard.Faithfulness` pair; its image-factorization
proof is reused without modification.

## Development checks

Approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the
proof without warnings or errors in diagnostic
`155d36c3-ecfe-4c3d-92f4-2ffad30f2894`. Lake build and declaration inspection
`a8ca054e-6ea5-4666-a7ea-757a60d96b7e` also completed without warnings or
errors. A private diagnostic printed all four unapplied theorem types and
assigned them to their complete telescopes; it additionally assigned the
aggregate to the expanded conjunction above. Inspection confirms independent
level parameters `v, u` and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. The inspected aggregate type has SHA256
`1cd070cea1b3b56dca7c41167e5e0575e1dd33d0570a1326973253800e458e62`.
These are development checks; independent semantic review, official
exact-target validation and publication are separate requirements.
