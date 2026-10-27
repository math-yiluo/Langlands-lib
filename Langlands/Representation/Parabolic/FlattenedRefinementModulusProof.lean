import Langlands.Representation.Parabolic.FlattenedRefinementModulusStatement
import Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation

/-! Proof of the closed full modulus comparison for flattened block refinements. -/

namespace Langlands.Parabolic

universe uF

/-- The composed modulus pulled back along the flattened Levi equivalence is
the full modulus of the flattened shape, for all parameters. -/
theorem flattenedRefinementModulus :
    FlattenedRefinementModulusStatement.{uF} := by
  intro p _ F T n B S
  exact T.composedLeviModulus_flattened B S

end Langlands.Parabolic
