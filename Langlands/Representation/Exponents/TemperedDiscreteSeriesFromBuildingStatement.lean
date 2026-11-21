import Langlands.Geometry.Building.GroupAxiomsExistenceStatement
import Langlands.Representation.Exponents.TemperedIrreducibleDiscreteSeriesStatement
import Langlands.Representation.Exponents.TemperedIrreducibleUnitarizableStatement
import Langlands.Representation.Exponents.TemperedSquareIntegrableUnitaryPartStatement

/-! # The tempered square-integrability criterion and discrete series from building data -/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- Existence of data satisfying the one-group building axioms implies the
square-integrability criterion of VII.2.4, the discrete-series embedding
equivalence of VII.2.6, and its unitarizability corollary. -/
def TemperedDiscreteSeriesFromBuildingStatement : Prop :=
  Geometry.Building.GroupAxiomsExistenceStatement.{u} →
    TemperedSquareIntegrableUnitaryPartStatement.{u, v} ∧
      TemperedIrreducibleDiscreteSeriesStatement.{u, v} ∧
      TemperedIrreducibleUnitarizableStatement.{u, v}

end Langlands.Aubert.General.RepresentedParabolic
