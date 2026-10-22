import Langlands.Weil.Representation.UnramifiedReductionProof
import Langlands.Weil.Representation.FiniteImageExtensionProof

namespace Langlands.Weil

universe uW uV

/-- The complete finite-image and unramified-reduction statement family. -/
theorem representationStructure : RepresentationStructure.{uW, uV} :=
  ⟨unramifiedReduction.{uW, uV}, finiteImageExtension.{uW, uV}⟩

end Langlands.Weil
