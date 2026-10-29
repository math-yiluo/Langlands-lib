import Langlands.CategoryTheory.Renard.FinitePreservationStatements
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Sequence exactness and finite preservation

The one-sided comparisons reuse the exact one-sided entries of Mathlib's
TFAE theorems. The joint comparison combines them using Renard's definition.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace Langlands.Renard

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- Renard's actual left sequence condition is finite-limit preservation. -/
theorem sequenceLeftExactFiniteLimits : SequenceLeftExactFiniteLimitsStatement F := by
  exact (Functor.preservesFiniteLimits_tfae F).out 2 4

/-- Renard's actual right sequence condition is finite-colimit preservation. -/
theorem sequenceRightExactFiniteColimits : SequenceRightExactFiniteColimitsStatement F := by
  exact (Functor.preservesFiniteColimits_tfae F).out 2 4

/-- Two-sided sequence exactness is simultaneous finite preservation by the same functor. -/
theorem sequenceExactFinitePreservation : SequenceExactFinitePreservationStatement F := by
  exact and_congr (sequenceLeftExactFiniteLimits F) (sequenceRightExactFiniteColimits F)

/-- The exact published aggregate of the three finite-preservation comparisons. -/
theorem finitePreservationComparison : FinitePreservationComparisonStatement F := by
  exact ⟨sequenceLeftExactFiniteLimits F,
    sequenceRightExactFiniteColimits F, sequenceExactFinitePreservation F⟩

end Langlands.Renard
