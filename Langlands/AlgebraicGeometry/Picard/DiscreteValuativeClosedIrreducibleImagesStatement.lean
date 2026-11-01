import Langlands.AlgebraicGeometry.Picard.ClosedIrreducibleImages
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Closed irreducible images detected by discrete valuation rings -/

universe u

open AlgebraicGeometry CategoryTheory

namespace Langlands.AlgebraicGeometry

namespace DiscreteValuativeCriterion

/-- The existence part of the valuative criterion, tested only on discrete valuation rings. -/
def Existence {X S : Scheme.{u}} (p : X ⟶ S) : Prop :=
  ∀ sq : ValuativeCommSq p, IsDiscreteValuationRing sq.R → sq.commSq.HasLift

/-- Full valuative existence implies existence for the discrete tests. -/
theorem of_valuativeCriterionExistence {X S : Scheme.{u}} (p : X ⟶ S)
    (hp : ValuativeCriterion.Existence p) : Existence p :=
  fun sq _ => hp sq

end DiscreteValuativeCriterion

/-- The displayed-base closed-image consequence of EGA IV 18.10.20. -/
def DiscreteValuativeClosedIrreducibleImagesStatement : Prop :=
  ∀ (X S : Scheme.{u}) [IsLocallyNoetherian S] (p : X ⟶ S)
    [LocallyOfFiniteType p] [IsSeparated p],
    DiscreteValuativeCriterion.Existence p → ClosedIrreducibleImages p

end Langlands.AlgebraicGeometry
