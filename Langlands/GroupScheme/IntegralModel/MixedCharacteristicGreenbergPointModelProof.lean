import Langlands.GroupScheme.IntegralModel.GreenbergMixed.Assembly
import Langlands.GroupScheme.IntegralModel.GreenbergDVR

/-! # Greenberg point models over mixed-characteristic DVRs (KP Theorem A.4.19)

The mixed-characteristic case of the Greenberg point-model theorem: the Witt-vector Greenberg
ring schemes (`GreenbergDVR`) feed the Greenberg group construction (`GreenbergMixed`).
-/

universe u

namespace Langlands.GroupScheme.IntegralModel

/-- **KP Theorem A.4.19, mixed characteristic (points form).** Over a discrete valuation ring
with algebraically closed residue field of a different characteristic, every smooth affine
group scheme has a Greenberg point model at every positive level. -/
theorem mixedCharacteristicGreenbergPointModel :
    MixedCharacteristicGreenbergPointModelStatement.{u} :=
  GreenbergMixed.mixedCharacteristicGreenbergPointModel_of_existence
    fun R _ _ _ _ hchar n => Greenberg.nonempty_greenbergRingScheme R hchar n

end Langlands.GroupScheme.IntegralModel
