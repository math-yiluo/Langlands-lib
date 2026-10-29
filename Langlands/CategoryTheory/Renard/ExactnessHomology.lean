import Langlands.CategoryTheory.Renard.ExactnessHomologyStatements
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Proof of the sequence-exactness, exact short complex and homology comparisons

Proof of `Langlands.Renard.ExactnessHomologyComparisonStatement` for every additive
functor between arbitrary abelian categories. Renard's two one-sided sequence conditions
are the second entries of Mathlib's `Functor.preservesFiniteLimits_tfae` and
`Functor.preservesFiniteColimits_tfae`; their fourth entries are finite-limit and
finite-colimit preservation, whose conjunction is the fourth entry of `Functor.exact_tfae`.
-/

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace Langlands.Renard

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]

/-- Renard's two-sided sequence exactness is preservation of finite limits and finite
colimits. This is an internal step of the proof below. -/
private theorem sequenceExact_iff_preservesFiniteLimits_and_preservesFiniteColimits
    (F : C ⥤ D) [F.Additive] :
    SequenceExact F ↔ PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
  and_congr ((Functor.preservesFiniteLimits_tfae F).out 2 4)
    ((Functor.preservesFiniteColimits_tfae F).out 2 4)

/-- Sequence exactness is preservation of every middle-exact short complex. -/
theorem sequenceExactShortComplex (F : C ⥤ D) [F.Additive] :
    SequenceExactShortComplexStatement F :=
  (sequenceExact_iff_preservesFiniteLimits_and_preservesFiniteColimits F).trans
    ((Functor.exact_tfae F).out 4 2)

/-- Sequence exactness is preservation of every short exact complex. -/
theorem sequenceExactShortExact (F : C ⥤ D) [F.Additive] :
    SequenceExactShortExactStatement F :=
  (sequenceExact_iff_preservesFiniteLimits_and_preservesFiniteColimits F).trans
    ((Functor.exact_tfae F).out 4 1)

/-- Sequence exactness is Mathlib's homology-preservation class. -/
theorem sequenceExactHomology (F : C ⥤ D) [F.Additive] :
    SequenceExactHomologyStatement F :=
  (sequenceExact_iff_preservesFiniteLimits_and_preservesFiniteColimits F).trans
    ((Functor.exact_tfae F).out 4 3)

/-- The aggregate of the three comparisons. -/
theorem exactnessHomologyComparison (F : C ⥤ D) [F.Additive] :
    ExactnessHomologyComparisonStatement F :=
  ⟨sequenceExactShortComplex F, sequenceExactShortExact F, sequenceExactHomology F⟩

end Langlands.Renard
