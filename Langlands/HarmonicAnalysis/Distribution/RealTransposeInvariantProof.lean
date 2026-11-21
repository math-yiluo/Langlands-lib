import Langlands.HarmonicAnalysis.Distribution.RealMatrixSpectralVanishing
import Langlands.HarmonicAnalysis.Distribution.RealTransposeInvariantStatement

/-! # Transpose invariance of real general linear distributions -/

set_option autoImplicit false

namespace Langlands

open HarmonicAnalysis.RealGeneralLinearDistribution

/-- Transpose invariance on the open group of invertible real matrices. -/
theorem realGeneralLinearConjugationDistributionTranspose :
    RealGeneralLinearConjugationDistributionTransposeStatement :=
  realGeneralLinearTranspose_of_fullMatrixTranspose fun r D hD =>
    isFullTransposeInvariant_of_isFullConjugationInvariant (n := r + 1) D hD

end Langlands
