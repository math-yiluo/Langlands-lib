# Sequence exactness, exact short complexes and homology

Authors: Worker 6 (statement specification, implementation and source/interface audit);
Worker 691 (direct source and interface verification, declaration checks and submission);
Worker 1055 (proof-status correction after the 29 October 2026 Library audit).

Module: `Langlands.CategoryTheory.Renard.ExactnessHomologyStatements`.
All four declarations are in namespace `Langlands.Renard`.
This is a statement unit: it defines three comparison propositions and their
conjunction. It proves none of the equivalences.

## Source and derived provenance

The source sequence-exactness predicate comes from David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, A.VIII.1, printed page 266 / PDF page 272. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`. The original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 6 and Worker 691 each read that page directly; Worker 691 rechecked
the original and supplementary errata on 28 October 2026. Renard assumes additive functors between abelian
categories, defines exactness as the conjunction of left and right sequence
exactness, and states that left exactness preserves finite limits and right
exactness preserves finite colimits.

The paragraph does not explicitly state the three equivalences in this module.
They are derived internal comparisons connecting the published sequence
predicate with existing Mathlib interfaces. The aggregate conjunction is
internal packaging. None is attributed as a separate explicit assertion in
the source. The published `Langlands.CategoryTheory.RenardExactFunctor`
contains the source predicates and their definitional unfolding laws; this
module imports them without alteration.

The available supplementary errata for the 2010 edition, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were checked on PDF pages 18–19. The correction on old printed page 308
changes faithful to exact in the argument about preserving epimorphisms and
monomorphisms; the governing 2026 text already uses exact. These errata do not
state the new comparison equivalences.

## Complete proposition declarations

The complete common context is

```lean
open CategoryTheory
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
```

The source and target object universes and the two Hom universes are
independent. Each declaration explicitly binds the actual functor and its
additivity instance. In this context the complete types and bodies are:

```lean
def SequenceExactShortComplexStatement (F : C ⥤ D) [F.Additive] : Prop :=
  SequenceExact F ↔
    (∀ S : ShortComplex C, S.Exact → (S.map F).Exact)

def SequenceExactShortExactStatement (F : C ⥤ D) [F.Additive] : Prop :=
  SequenceExact F ↔
    (∀ S : ShortComplex C, S.ShortExact → (S.map F).ShortExact)

def SequenceExactHomologyStatement (F : C ⥤ D) [F.Additive] : Prop :=
  SequenceExact F ↔ F.PreservesHomology

def ExactnessHomologyComparisonStatement (F : C ⥤ D) [F.Additive] : Prop :=
  SequenceExactShortComplexStatement F ∧
    (SequenceExactShortExactStatement F ∧ SequenceExactHomologyStatement F)
```

`SequenceExact F` is the published conjunction `SequenceLeftExact F ∧
SequenceRightExact F`. Its left condition tests all `S : ShortComplex C`
with `S.Exact ∧ Mono S.f`, and requires mapped middle exactness and
`Mono (F.map S.f)`. Its right condition tests all `S` with `S.Exact ∧
Epi S.g`, and requires mapped middle exactness and `Epi (F.map S.g)`.
These source conditions are not restricted to short exact inputs.

The first new proposition compares this conjunction with preservation of every
middle-exact short complex. Such a complex has actual arrows `S.f` and `S.g`
with zero composite; `S.Exact` means exactness at the middle object. Neither
boundary mono nor boundary epi is required in that right-hand condition.
The actual mapped complex `S.map F` uses objects `F.obj S.X₁`, `F.obj S.X₂`,
`F.obj S.X₃` and boundary arrows `F.map S.f`, `F.map S.g`.

The second proposition instead uses Mathlib's actual `S.ShortExact`, whose
fields are `S.Exact`, `Mono S.f` and `Epi S.g`. Its mapped conclusion includes
all three fields, so it includes both endpoint conditions. This is distinct
from preserving only middle exactness on short exact inputs.

The third proposition uses the actual Prop class
`CategoryTheory.Functor.PreservesHomology`, defined in
`Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean`. For a
zero-morphism-preserving functor, its fields assert, for every actual morphism
`f : X ⟶ Y`, `PreservesLimit (parallelPair f 0) F` and
`PreservesColimit (parallelPair f 0) F`: preservation of the actual kernel and
cokernel diagrams. The class is not replaced by existence of a homology object
or by a chosen homology isomorphism. Additivity supplies
`F.PreservesZeroMorphisms`, used both by this class and by `S.map F`.

No smallness, concreteness, finite-dimensionality, module, representation or
additional completeness premise is imposed. Abelian structures supply the
categorical setting. No finite-preservation or homology-preservation instance,
exactness comparison, or desired conclusion is assumed as a premise of these
definitions.

## Proof route and related results

At Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`, the actual
`Functor.preservesFiniteLimits_tfae F` and
`Functor.preservesFiniteColimits_tfae F` compare their second entries, which
are the published one-sided sequence conditions, with finite preservation.
`Functor.exact_tfae F` relates preservation of short exact complexes,
preservation of every middle-exact short complex, the actual
`F.PreservesHomology` class, and the conjunction of finite-limit and
finite-colimit preservation. These declarations are in
`Mathlib/Algebra/Homology/ShortComplex/ExactFunctor.lean`, which was read in
full for this interface audit. Their category parameters allow the four
independent universes used here. This statement module implements no adapter
theorem. The separate proof `exactnessHomologyComparison` in
`Langlands.CategoryTheory.Renard.ExactnessHomology` follows this route. It
proves `ExactnessHomologyComparisonStatement F` for every additive functor `F`
between abelian categories, with independent object universes `u₁`, `u₂` and
Hom universes `v₁`, `v₂`.

The related comparisons are separate units with their own published proofs,
none of which is imported here:

- `FinitePreservationComparisonStatement F`, in
  `Langlands.CategoryTheory.Renard.FinitePreservationStatements`, is proved by
  `finitePreservationComparison` in
  `Langlands.CategoryTheory.Renard.FinitePreservation`;
- `FaithfulnessCriteriaStatement F`, in
  `Langlands.CategoryTheory.Renard.FaithfulnessStatements`, is proved by
  `faithfulnessCriteria` in `Langlands.CategoryTheory.Renard.Faithfulness`.

Both have the same additive-functor hypotheses and the same four independent
universes as `exactnessHomologyComparison`. The Hom object properties are
defined in `Langlands.CategoryTheory.Renard.HomObjectProperties`. For an object
`P` of one abelian category, `HomExactnessComparisonStatement P` and
`HomGeneratorCriteriaStatement P` are proved by `homExactnessComparison` in
`Langlands.CategoryTheory.Renard.HomExactnessComparison` and by
`homGeneratorCriteria` in `Langlands.CategoryTheory.Renard.HomGeneratorCriteria`.
This unit constructs no chain-complex functor or natural homology comparison
isomorphism and states no such complex-level comparison target.

Its parent whole-book responsibility is `f5d1f399-a1f8-4ab5-a981-90b92abd4857`
revision 2; its focused statement task is `2344b69e-42b7-4a4b-b933-e5e9641547cd`
revision 1.
