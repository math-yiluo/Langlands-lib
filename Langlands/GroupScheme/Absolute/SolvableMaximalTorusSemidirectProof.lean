import Langlands.GroupScheme.Absolute.TriangularTorusConjugacy
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Absolute.SolvableSplitExtensionProof

/-! # Smooth connected solvable groups as semidirect products with a maximal torus -/

universe u

namespace Langlands.GroupScheme

/-- Every smooth connected affine solvable group over an algebraically closed field is the
semidirect product of its unipotent part and any maximal torus (Milne 2017, 16.33(d)). -/
theorem solvableMaximalTorusSemidirect : SolvableMaximalTorusSemidirectStatement.{u} :=
  solvableMaximalTorusSemidirectStatement_of_solvableTorusQuotient solvableTorusQuotient
    solvableSplitExtension

end Langlands.GroupScheme
