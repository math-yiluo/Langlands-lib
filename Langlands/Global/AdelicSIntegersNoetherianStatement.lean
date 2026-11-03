import Langlands.Global.NumberFieldAdeleLevel
import Langlands.Global.CurvePlaceAdeleRing
import Mathlib.NumberTheory.FunctionField

/-! # Noetherianity targets for the actual arithmetic S-integer rings -/

universe u

namespace Langlands.Global

/-- The actual outside-`S` integer rings of a function field are Noetherian
and have dimension at most one, including for empty `S`. -/
def CurvePlaceSIntegersNoetherianStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
    (S : Finset (AlgebraicCurve.Place k F)),
    IsNoetherianRing (curvePlaceSIntegers k F S) ∧
      Ring.DimensionLEOne (curvePlaceSIntegers k F S)

/-- The actual outside-`S` integer rings of a number field are Noetherian
and have dimension at most one. -/
def NumberFieldSIntegersNoetherianStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K)),
    IsNoetherianRing ((S : Set (FinitePlace K)).integer K) ∧
      Ring.DimensionLEOne ((S : Set (FinitePlace K)).integer K)

/-- Arithmetic Noetherianity in both characteristics. -/
def AdelicSIntegersNoetherianStatement : Prop :=
  CurvePlaceSIntegersNoetherianStatement.{u} ∧
    NumberFieldSIntegersNoetherianStatement.{u}

end Langlands.Global
