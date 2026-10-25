import Langlands.AlgebraicGeometry.FieldSmoothProperConnectedGlobalFunctions
import Langlands.AlgebraicGeometry.GlobalFunctionsFieldProof

universe u

namespace Langlands.AlgebraicGeometry

/-- The canonical global-section map of a smooth proper geometrically connected
scheme over any field is an isomorphism. -/
theorem fieldSmoothProperConnectedGlobalFunctions :
    FieldSmoothProperConnectedGlobalFunctions.{u} := by
  intro K _ X p hs hp hg
  exact @GlobalFunctionsFieldProof.isIso_appTop_of_field K _ X p hs hp hg

end Langlands.AlgebraicGeometry
