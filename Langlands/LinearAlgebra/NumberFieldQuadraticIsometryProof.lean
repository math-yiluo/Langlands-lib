import Langlands.ClassField.Global.CyclicHasseNormProof
import Langlands.LinearAlgebra.NumberFieldQuadraticIsometryReduction
import Langlands.LinearAlgebra.NumberFieldQuadraticIsotropyOfCyclicNorm

/-! # The Hasse–Minkowski isometry theorem over number fields -/

universe u

namespace Langlands

/-- Quadratic forms over a number field are isometric if their actual scalar
extensions to every completion are isometric and both forms are nondegenerate. -/
theorem numberFieldQuadraticIsometry : NumberFieldQuadraticIsometryStatement.{u} :=
  numberFieldQuadraticIsometry_of_isotropy
    (numberFieldQuadraticIsotropy_of_cyclicNorm ClassField.Global.cyclicHasseNorm)

end Langlands
