import Langlands.Representation.GodementJacquet.GenericMatrixFunctionalEquationReductionProof
import Langlands.Representation.GodementJacquet.TateMatrixFunctionalEquationProof
import Langlands.Representation.GodementJacquet.SupercuspidalMatrixFunctionalEquationProof

/-! Normalized matrix functional-equation data on the actual generic representation. -/

namespace Langlands.GodementJacquet

universe uF uV

/-- Full matrix data for every irreducible Whittaker-type representation. -/
theorem genericMatrixFunctionalEquation :
    GenericMatrixFunctionalEquationStatement.{uF,uV} :=
  genericMatrixFunctionalEquationReduction.{uF,uV}
    tateMatrixFunctionalEquation.{uF,uV}
    supercuspidalMatrixFunctionalEquation.{uF,uV}

end Langlands.GodementJacquet
