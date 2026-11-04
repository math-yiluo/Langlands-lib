import Langlands.Global.AdelicLevelModelPoints
import Mathlib.Topology.Algebra.IsOpenUnits

/-! # Open units in the actual local factors of adelic levels -/

universe u

namespace Langlands.Global

/-- Open units, with their existing value-and-inverse topology, in every actual
curve-place factor and every actual full number-field factor. -/
def AdelicLocalFactorUnitsStatement : Prop :=
  (∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    (S : Finset (AlgebraicCurve.Place k F)) (i : CurvePlaceLevelFactorIndex k F S),
    IsOpenUnits (CurvePlaceLevelFactor k F S i)) ∧
  (∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (FinitePlace K)) (i : NumberFieldLevelFactorIndex K S),
    IsOpenUnits (NumberFieldLevelFactor K S i))

end Langlands.Global
