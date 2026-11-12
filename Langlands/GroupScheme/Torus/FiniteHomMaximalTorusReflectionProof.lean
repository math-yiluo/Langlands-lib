import Langlands.GroupScheme.Torus.FiniteHomMaximalityStatement
import Langlands.GroupScheme.Torus.FiniteHomMaximalityReduction
import Langlands.GroupScheme.Torus.ImageProof

/-!
# Proof of `Langlands.GroupScheme.FiniteHomMaximalTorusReflectionStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme

/-- Proof of `FiniteHomMaximalTorusReflectionStatement`. -/
theorem finiteHomMaximalTorusReflection : FiniteHomMaximalTorusReflectionStatement.{u} :=
  finiteHomMaximalTorusReflection_of_torusImage torusImageClosedTorusStatement

end Langlands.GroupScheme
