import Langlands.GroupScheme.Reductive.CharZeroInvariantIntegral
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicityProof

/-! # Splitting of reductive extensions by vector kernels in characteristic zero -/

universe u

namespace Langlands.GroupScheme

/-- Over a field of characteristic zero, every faithfully flat homomorphism from an
affine group scheme onto a connected reductive group whose full kernel is a vector
group has a homomorphic section over the original field. -/
theorem characteristicZeroReductiveVectorExtension :
    CharacteristicZeroReductiveVectorExtensionStatement.{u} :=
  characteristicZeroReductiveVectorExtension_of_semisimplicity
    reductiveCharZeroSemisimplicityStatement

end Langlands.GroupScheme
