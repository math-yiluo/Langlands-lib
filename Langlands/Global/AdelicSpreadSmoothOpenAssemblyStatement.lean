import Langlands.Global.AdelicSpreadSmoothOpenStatement
import Langlands.Global.AdelicSmoothLocalOpenStatement
import Langlands.Global.AdelicModelOpenReductionStatement
import Langlands.Global.AdelicSpreadGeometricallyConnectedStatement
import Langlands.Global.AdelicLevelComponentSurjectivityStatement

/-! # Conrad's Theorem 4.5 from its model, local and almost-all inputs -/

universe u

namespace Langlands.Global

/-- Function fields: uniform Lang-Weil, almost-all level surjectivity, local
smooth openness, the fixed-model product reduction and compatible smooth
geometrically connected models together give adelic openness for arbitrary
finite-type spreads. -/
def CurvePlaceSpreadSmoothOpenAssemblyStatement : Prop :=
  Langlands.AlgebraicGeometry.UniformLangWeilStatement.{u} →
    CurvePlaceLevelComponentSurjectivityStatement.{u} →
    CurvePlaceSmoothLocalPointOpenStatement.{u} →
    CurvePlaceFixedModelAdeleOpenOfLocalStatement.{u} →
    CurvePlaceSpreadMorphismPropertyExistenceStatement.{u}
      (@_root_.AlgebraicGeometry.Smooth ⊓ @_root_.AlgebraicGeometry.GeometricallyConnected) →
    CurvePlaceSpreadSmoothOpenStatement.{u}

/-- Number fields: the same inputs for the original integer rings, with every
infinite factor retained, give full-adele openness for arbitrary spreads. -/
def NumberFieldSpreadSmoothOpenAssemblyStatement : Prop :=
  Langlands.AlgebraicGeometry.UniformLangWeilStatement.{u} →
    NumberFieldLevelComponentSurjectivityStatement.{u} →
    NumberFieldSmoothLocalPointOpenStatement.{u} →
    NumberFieldFixedModelAdeleOpenOfLocalStatement.{u} →
    NumberFieldSpreadMorphismPropertyExistenceStatement.{u}
      (@_root_.AlgebraicGeometry.Smooth ⊓ @_root_.AlgebraicGeometry.GeometricallyConnected) →
    NumberFieldSpreadSmoothOpenStatement.{u}

/-- The assembly of Conrad's Theorem 4.5 in both characteristics from its
separately stated inputs. -/
def AdelicSpreadSmoothOpenAssemblyStatement : Prop :=
  CurvePlaceSpreadSmoothOpenAssemblyStatement.{u} ∧
    NumberFieldSpreadSmoothOpenAssemblyStatement.{u}

end Langlands.Global
