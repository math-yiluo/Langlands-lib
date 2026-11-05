import Langlands.FieldTheory.DimensionLEOne
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! # Dimension at most one for Henselian discretely valued fields -/

universe u

namespace Langlands.FieldTheory

/-- A Henselian discretely valued field with algebraically closed residue
satisfies the finite-separable norm criterion for dimension at most one. -/
def HenselianDiscreteDimensionLEOneStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (v : Valuation K (WithZero (Multiplicative ℤ))),
    Function.Surjective v →
    HenselianLocalRing v.valuationSubring →
    IsAlgClosed (IsLocalRing.ResidueField v.valuationSubring) →
    HasDimensionLEOne K

end Langlands.FieldTheory
