import Langlands.Representation.GodementJacquet.GenericMatrixFunctionalEquationStatement
import Langlands.Representation.GodementJacquet.TateMatrixFunctionalEquationStatement
import Langlands.Representation.GodementJacquet.SupercuspidalMatrixFunctionalEquationStatement

/-! Internal reduction of irreducible matrix data to the two analytic bases. -/

namespace Langlands.GodementJacquet

universe uF uV

/-- Conditional reduction only; both analytic bases remain explicit premises. -/
def GenericMatrixFunctionalEquationReductionStatement : Prop :=
  TateMatrixFunctionalEquationStatement.{uF,uV} →
  SupercuspidalMatrixFunctionalEquationStatement.{uF,uV} →
  GenericMatrixFunctionalEquationStatement.{uF,uV}

end Langlands.GodementJacquet
