import Langlands.Representation.Parabolic.RefinementCoordinatesModulusStatement
import Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationProof

/-! The full determinant modulus under ordered refinement coordinates. -/

namespace Langlands.Parabolic

universe uF

/-- Ordered refinement coordinates identify the composed full modulus with the
full modulus of the target block shape. -/
theorem refinementCoordinatesModulus :
    RefinementCoordinatesModulusTheorem.{uF} := by
  intro p _ F T n B D S e hs hc
  exact RefinementCoordinatesNormalization.modulus_of_coordinates F T B D S e hs hc

end Langlands.Parabolic
