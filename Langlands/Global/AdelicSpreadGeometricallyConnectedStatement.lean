import Langlands.Global.AdelicSpreadEventualSmoothFiberGeometryStatement
import Langlands.Global.AdelicSpreadSmoothExistenceStatement
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Geometrically connected arithmetic models without a common fibre dimension -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- Geometric connectedness is detected at an actual function-field integer
superlevel, also simultaneously with smoothness. Compatible separated
finite-type models realize the combined property. -/
def CurvePlaceSpreadGeometricallyConnectedStatement : Prop :=
  CurvePlaceSpreadEventualPropertyStatement.{u} @GeometricallyConnected ∧
    CurvePlaceSpreadEventualPropertyStatement.{u} (@Smooth ⊓ @GeometricallyConnected) ∧
    CurvePlaceSpreadMorphismPropertyExistenceStatement.{u}
      (@Smooth ⊓ @GeometricallyConnected)

/-- The same three assertions for the original number-field integer rings. -/
def NumberFieldSpreadGeometricallyConnectedStatement : Prop :=
  NumberFieldSpreadEventualPropertyStatement.{u} @GeometricallyConnected ∧
    NumberFieldSpreadEventualPropertyStatement.{u} (@Smooth ⊓ @GeometricallyConnected) ∧
    NumberFieldSpreadMorphismPropertyExistenceStatement.{u}
      (@Smooth ⊓ @GeometricallyConnected)

/-- Actual arithmetic descent and compatible smooth geometrically connected
models in both characteristics, with no supplied common fibre dimension. -/
def AdelicSpreadGeometricallyConnectedStatement : Prop :=
  CurvePlaceSpreadGeometricallyConnectedStatement.{u} ∧
    NumberFieldSpreadGeometricallyConnectedStatement.{u}

end Langlands.Global
