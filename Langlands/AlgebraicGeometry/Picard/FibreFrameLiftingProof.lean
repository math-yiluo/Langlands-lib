import Langlands.AlgebraicGeometry.Picard.FibreFrameLifting.Assembly
import Langlands.AlgebraicGeometry.Modules.RestrictionPerfectModelsProof
import Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadProof

/-!
# Local fibre frame lifting detected by two closed restrictions: proof

`FibreFrameLiftingStatement` follows from the conditional assembly
`FibreFrameLifting.fibreFrameLifting_of_models`, applied to the published proof
`restrictionPerfectModels` of `RestrictionPerfectModelsStatement` and to the published proof
`fibreH0RestrictionSpread` of `FibreH0RestrictionSpreadStatement`.
-/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- A line bundle on a smooth proper geometrically connected family that is trivial on the fibre
over `s` and on two closed subfamilies whose fibre restrictions jointly detect `H¹` of the fibre
has a section near `s` whose restriction to the fibre is a frame. -/
theorem fibreFrameLifting : FibreFrameLiftingStatement.{u} :=
  FibreFrameLifting.fibreFrameLifting_of_models Modules.restrictionPerfectModels
    Cohomology.ModuleComplex.fibreH0RestrictionSpread

end Langlands.AlgebraicGeometry.Picard
