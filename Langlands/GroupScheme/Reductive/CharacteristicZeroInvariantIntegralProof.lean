import Langlands.GroupScheme.Reductive.CharZeroInvariantIntegral
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicityProof

/-! # characteristicZeroReductiveInvariantIntegral: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme

/-- Every connected reductive affine group over a characteristic-zero field admits normalized invariant integration on its actual coordinate algebra, with the original all-coefficient-algebra invariance. -/
theorem characteristicZeroReductiveInvariantIntegral :
    CharacteristicZeroReductiveInvariantIntegralStatement.{u} :=
  characteristicZeroReductiveInvariantIntegral_of_semisimplicity
    reductiveCharZeroSemisimplicityStatement

end Langlands.GroupScheme
