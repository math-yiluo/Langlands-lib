import Langlands.Representation.Smooth.RenardRegularHeckeProof
import Langlands.Representation.Smooth.RenardTensorHomExactnessProof

/-! # Renard III.1.2, III.1.3 and III.1.15: the combined proof -/

universe u v

namespace Langlands.Renard.Smooth

/-- Regular smoothness, convolution action and the smooth tensor–Hom theorems. -/
theorem renardTensorHomStatements : RenardTensorHomStatements.{u, v} :=
  ⟨regularRepresentationSmooth, leftRegularHeckeAction, tensorHomAdjunction, tensorHomExactness⟩

end Langlands.Renard.Smooth
