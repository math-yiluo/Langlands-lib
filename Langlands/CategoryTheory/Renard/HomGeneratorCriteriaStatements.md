# Renard A.VIII.2: generator comparisons and the nonzero-Hom criterion

Authors: Worker 6 (original shared draft: Lean declarations and
documentation), Worker 932 (independent source and declaration re-checks,
documentation refinements and submission).

This statement unit uses the object properties from
`Langlands.CategoryTheory.Renard.HomObjectProperties` and the actual Hom
functors from `Langlands.CategoryTheory.Renard.HomFunctors`. Its four
declarations belong to namespace `Langlands.Renard` in module
`Langlands.CategoryTheory.Renard.HomGeneratorCriteriaStatements`.
They define propositions; they supply no proofs of those propositions.

## Original source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.VIII.2,
printed page 267 / PDF page 273. The Hom introduction and the exact-functor
faithfulness lemma are on printed page 266 / PDF page 272. Both complete
pages were read. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Renard defines a generator by faithfulness of the covariant Hom functor, a
cogenerator by faithfulness of the contravariant Hom functor, and a
progenerator as a projective generator. He then explicitly states the
unnumbered criterion: a projective object is a progenerator if and only if
its Hom group into every nonzero object is nontrivial. The sufficiency
direction is attributed to the preceding exact-functor faithfulness lemma.
`ProjectiveProgeneratorCriterionStatement` states this source assertion.
The source sentence reads: « Un critère simple est qu'un objet projectif
𝑋 est un progénérateur dans 𝒜 si et seulement si pour tout objet non nul
𝑌 dans 𝒜, Hom_𝒜(𝑋, 𝑌) est non trivial. Cette condition est suffisante en
vertu du lemme A.VIII.1. » The source's object `X` is named `P` here.
« non nul » is rendered by `¬IsZero Y`, and « non trivial » for the
abelian group `Hom_𝒜(X, Y)` by the existence of an element different from
zero, that is, a morphism `f : P ⟶ Y` with `f ≠ 0`. The same page also
asserts that both Hom functors are left exact; that assertion belongs to
the separate Hom-exactness statements and is not stated here.

The supplementary author errata for the 2010 edition,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were reread at their appendix entries on PDF pages 18–19. They correct the
old reference to necessity to say that the condition is sufficient, and
replace faithfulness by exactness in the preceding image-factorization
argument. The governing 2026 text already incorporates both corrections.
The 2010 errata are supplementary evidence, not the governing edition.

The first two comparisons below are derived statements identifying the
source's faithful-Hom definitions with Mathlib's intrinsic separator and
coseparator predicates. Renard does not state these Mathlib comparisons.
The final conjunction is an internal grouping of the three propositions
for this review unit.

## Setting and actual Hom functors

Every declaration has precisely the common context

```lean
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
```

and an explicit object argument `(P : C)`. The object universe `u` and the
Hom universe `v` are independent. No cocompleteness, smallness,
Grothendieck, enough-projectives, enough-injectives, concreteness, module
category or finite-dimensionality assumption is imposed on `C`.

The imported functors, in namespace `Langlands.CategoryTheory.Renard`, are

```lean
preadditiveCoyonedaInt (P : C) : C ⥤ ModuleCat.{v} ℤ
preadditiveYonedaInt (P : C) : Cᵒᵖ ⥤ ModuleCat.{v} ℤ
```

The first has carrier `P ⟶ X` and sends `g : X ⟶ Y` to the linear map
`f ↦ f ≫ g`. The second has carrier `X ⟶ P` at `op X` and sends `g.op`
to the linear map `h ↦ g ≫ h`. These are the published restriction-of-scalars
constructions with the canonical integer actions on the Hom groups, and
both are additive. The source's contravariant functor is represented as a
covariant functor on `Cᵒᵖ`. The published Hom-functor documentation explains
the well-typed reading of the source's displayed composition labels.

`HomGenerator P` is faithfulness of the first actual functor;
`HomCogenerator P` is faithfulness of the second. Faithfulness tests
injectivity of the functor's map on every Hom type. Thus generation tests
whether equality of the linear maps induced by any parallel `f g : X ⟶ Y`
implies `f = g`, and cogeneration makes the corresponding test on the
opposite category. These are tests on all parallel arrows.

`HomProjective P` is the published `SequenceExact` condition on the actual
covariant integer-module Hom functor. This means both one-sided sequence
conditions: an exact `ShortComplex C` whose first arrow is mono remains
exact with mono first arrow, and an exact `ShortComplex C` whose second
arrow is epi remains exact with epi second arrow. The input is not
restricted to a short exact complex. `HomProgenerator P` is the published
conjunction `HomProjective P ∧ HomGenerator P`.

## Exact statement declarations

With the common binders above, the complete declarations are:

```lean
def HomGeneratorComparisonStatement (P : C) : Prop :=
  HomGenerator P ↔ CategoryTheory.IsSeparator P

def HomCogeneratorComparisonStatement (P : C) : Prop :=
  HomCogenerator P ↔ CategoryTheory.IsCoseparator P

def ProjectiveProgeneratorCriterionStatement (P : C) : Prop :=
  HomProjective P →
    (HomProgenerator P ↔
      ∀ Y : C, ¬CategoryTheory.Limits.IsZero Y → ∃ f : P ⟶ Y, f ≠ 0)

def HomGeneratorCriteriaStatement (P : C) : Prop :=
  HomGeneratorComparisonStatement P ∧
    HomCogeneratorComparisonStatement P ∧
    ProjectiveProgeneratorCriterionStatement P
```

These are Mathlib's actual predicates from
`Mathlib.CategoryTheory.Generator.Basic`, imported through
`Mathlib.CategoryTheory.Generator.Preadditive`. Literally,
`IsSeparator P` is `ObjectProperty.IsSeparating (.singleton P)` and
`IsCoseparator P` is `ObjectProperty.IsCoseparating (.singleton P)`.
Mathlib's `isSeparator_def` and `isCoseparator_def` unfold these to the full
parallel-morphism tests: `IsSeparator P` says that for all `X Y : C` and all
parallel `f g : X ⟶ Y`,
`(∀ h : P ⟶ X, h ≫ f = h ≫ g) → f = g`,
and `IsCoseparator P` says instead
`(∀ h : Y ⟶ P, f ≫ h = g ≫ h) → f = g`.
Neither test is restricted to nonzero objects or to a single morphism
compared with zero. Neither comparison has a projectivity premise. The
native predicates occur as conclusions of comparisons, not as additional
assumptions.

Projectivity is a premise only inside the third proposition. Its
quantifier ranges over every actual object `Y : C`. The predicate
`CategoryTheory.Limits.IsZero Y` intrinsically says that `Y` is a zero
object; it does not choose a presentation of `Y` or require an equality
with a selected zero object. The nontrivial Hom group is expressed by an
actual morphism `f : P ⟶ Y` with `f ≠ 0`. Mere inhabitation of the Hom type
would be insufficient, since the zero morphism always inhabits it.

The aggregate is the right-associated conjunction of the three preceding
propositions in that order. All four declarations return `Prop`. No
conclusion is an input hypothesis.

## Proof boundary

This unit supplies statement targets only. A distinct proof unit must
prove the two comparisons, the projective nonzero-Hom criterion and their
aggregate after these targets have been independently accepted and
published. Mathlib's faithful preadditive Hom comparisons provide proof
navigation; their presence does not itself prove the comparisons with the
imported integer-module functors.

Hom left exactness and the projective/injective lifting comparisons,
smallness and preservation of coproducts, finite-support factorization,
the finite-type comparison, presentations by sums of copies of `P`, and
the equivalence with right modules over `End P` remain separate
obligations. This unit assumes none of their conclusions.
