import Langlands.Global.Arithmetic.SplitQuadraticAssembly
import Langlands.Global.Arithmetic.PadicSquareNonsquareProof
import Langlands.Global.Arithmetic.QuadraticPadicSplittingProof

/-! # Split auxiliary quadratic fields in a common algebraic closure -/

namespace Langlands.Global

universe u

/-- Split imaginary and real quadratic fields with compositum linearly disjoint
from the supplied totally real number field. -/
theorem splitAuxiliaryQuadratics : SplitAuxiliaryQuadraticsStatement.{u} :=
  splitAuxiliaryQuadratics_of_prerequisites
    ⟨padicSquareNonsquare.{u}, quadraticPadicSplitting.{u}⟩

end Langlands.Global
