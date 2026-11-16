import Langlands.GroupScheme.IntegralModel.EqualCharacteristicGreenbergProof
import Langlands.GroupScheme.IntegralModel.MixedCharacteristicGreenbergPointModelProof

/-! # Greenberg point models at every positive congruence level -/

universe u

namespace Langlands.GroupScheme.IntegralModel

/-- **Greenberg point models (from KP Theorem A.4.19).** Every smooth affine group over
a DVR with algebraically closed residue field has the required smooth affine point
model at every positive congruence level, with source naturality and preservation of
geometric connectedness. -/
theorem greenbergPointModel : GreenbergPointModelStatement.{u} :=
  greenbergPointModel_of_characteristicCases
    equalCharacteristicGreenbergPointModel.{u}
    mixedCharacteristicGreenbergPointModel.{u}

end Langlands.GroupScheme.IntegralModel
