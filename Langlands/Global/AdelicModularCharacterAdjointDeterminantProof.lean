import Langlands.Global.AdelicLocalModularComparison
import Langlands.Global.LocalModularCharacterAdjointDeterminantProof

/-! # The adelic modular character is the normalized idele norm of `det Ad` -/

universe u

namespace Langlands.Global.AdelicGroupPoints

/-- The actual adelic modular character is the normalized idele norm of the
actual adjoint-determinant character. -/
theorem adelicModularCharacterAdjointDeterminant :
    AdelicModularCharacterAdjointDeterminantStatement.{u} :=
  adelicModularCharacterAdjointDeterminantStatement_of_local
    PlaceGroupPoints.localModularCharacterAdjointDeterminant.{u}

end Langlands.Global.AdelicGroupPoints
