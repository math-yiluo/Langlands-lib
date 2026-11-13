import Langlands.Geometry.Building.MaximalUnramifiedValuation

/-! # Integer normalization on finite extensions of the maximal unramified field -/

noncomputable section

universe u

namespace Langlands.Geometry.Building.Kottwitz

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F))

/-- An integer valuation with the actual spectral valuation's ordering and full value group.
Its source-positive order is `IntegerValuation.orderUnits v`. -/
def IsNormalizedIntermediateValuation
    (v : Valuation L (WithZero (Multiplicative ℤ))) : Prop :=
  v.IsEquiv (intermediateValuation F L) ∧ Function.Surjective v

/-- The integer normalization selected by its valuation ordering and surjectivity.
The unconditional existence and uniqueness obligation is
`NormalizedIntermediateValuationStatement`. -/
def normalizedIntermediateValuation : Valuation L (WithZero (Multiplicative ℤ)) := by
  classical
  letI : Nonempty (Valuation L (WithZero (Multiplicative ℤ))) := ⟨1⟩
  exact Classical.epsilon (IsNormalizedIntermediateValuation F L)

/-- Choice by characterization supplies its law whenever a normalized valuation exists. -/
theorem normalizedIntermediateValuation_spec
    (h : ∃ v, IsNormalizedIntermediateValuation F L v) :
    IsNormalizedIntermediateValuation F L (normalizedIntermediateValuation F L) := by
  classical
  exact Classical.epsilon_spec h

end Langlands.Geometry.Building.Kottwitz
