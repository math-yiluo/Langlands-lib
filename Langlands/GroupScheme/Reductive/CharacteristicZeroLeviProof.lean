import Langlands.GroupScheme.Reductive.CharacteristicZeroLeviAssembly
import Langlands.GroupScheme.Reductive.CharacteristicZeroVectorExtensionProof

/-! # Levi decomposition in characteristic zero -/

universe u

namespace Langlands.GroupScheme

/-- Every smooth connected affine group scheme of finite type over a
characteristic-zero field admits the split reductive quotient and smooth
connected unipotent full kernel of the published Levi statement. -/
theorem characteristicZeroLeviDecomposition :
    CharacteristicZeroLeviDecompositionStatement.{u} :=
  characteristicZeroLeviDecomposition_of_reductiveVectorExtensions
    characteristicZeroReductiveVectorExtension

end Langlands.GroupScheme
