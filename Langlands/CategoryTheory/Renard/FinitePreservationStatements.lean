import Langlands.CategoryTheory.RenardExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Sequence exactness and finite preservation

Renard A.VIII.1 states the two forward implications. The converses and
the joint comparison are derived comparisons with Mathlib's actual
preservation predicates. This file defines their proposition targets.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace Langlands.Renard

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]

/-- Source left sequence exactness compared with actual finite-limit preservation. -/
def SequenceLeftExactFiniteLimitsStatement : Prop :=
  SequenceLeftExact F ↔ PreservesFiniteLimits F

/-- Source right sequence exactness compared with actual finite-colimit preservation. -/
def SequenceRightExactFiniteColimitsStatement : Prop :=
  SequenceRightExact F ↔ PreservesFiniteColimits F

/-- Two-sided source exactness compared with preservation of both kinds of finite diagram. -/
def SequenceExactFinitePreservationStatement : Prop :=
  SequenceExact F ↔ (PreservesFiniteLimits F ∧ PreservesFiniteColimits F)

/-- Aggregate target for the three finite-preservation comparisons. -/
def FinitePreservationComparisonStatement : Prop :=
  SequenceLeftExactFiniteLimitsStatement F ∧
    (SequenceRightExactFiniteColimitsStatement F ∧
      SequenceExactFinitePreservationStatement F)

end Langlands.Renard
