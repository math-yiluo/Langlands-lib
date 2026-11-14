import Langlands.Representation.GodementJacquet.GenericMatrixFunctionalEquationReductionStatement
import Langlands.AllField.Representation.GodementJacquet.GenericMatrixFunctionalEquationStatement
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalMatrixFunctionalEquationStatement
import Langlands.AllField.Representation.GodementJacquet.TateMatrixFunctionalEquationStatement
/-! Internal reduction of irreducible matrix data to the two analytic bases. -/

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding GenericMatrixFunctionalEquationReductionStatement GenericMatrixFunctionalEquationStatement SupercuspidalMatrixFunctionalEquationStatement TateMatrixFunctionalEquationStatement
open Langlands.AllField.GodementJacquet

universe uF uV

/-- Conditional reduction only; both analytic bases remain explicit premises. -/
def GenericMatrixFunctionalEquationReductionStatement : Prop :=
  TateMatrixFunctionalEquationStatement.{uF,uV} →
  SupercuspidalMatrixFunctionalEquationStatement.{uF,uV} →
  GenericMatrixFunctionalEquationStatement.{uF,uV}

end Langlands.AllField.GodementJacquet
