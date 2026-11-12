import Langlands.HarmonicAnalysis.Distribution.RenardConvolutionDensityProof

/-! # Renard II.3.10: all compact distribution convolution laws -/

namespace Langlands.HarmonicAnalysis.Distribution.RenardConvolution

universe uG

/-- All nine published convolution statements, at the full group universe. -/
theorem statements : Statements.{uG} :=
  ⟨ambientTensor, regularity, associativity, mixedAssociativity, haarDensity,
    evaluation, bilinearUnit, diracLaws, heckeCompatibility⟩

end Langlands.HarmonicAnalysis.Distribution.RenardConvolution
