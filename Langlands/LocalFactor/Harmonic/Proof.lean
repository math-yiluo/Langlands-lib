import Langlands.LocalFactor.Harmonic.NormalizationProof
import Langlands.HarmonicAnalysis.PadicFourierClosureProof
import Langlands.HarmonicAnalysis.PadicFourierScalingProof

/-! The complete p-adic Fourier and Haar-normalization theorem. -/

namespace Langlands.LocalFactors

universe u

/-- All five conclusions of the published harmonic-analysis proposition. -/
theorem padicHarmonicAnalysis : PadicHarmonicAnalysisStatement.{u} :=
  ⟨HarmonicAnalysis.padicFourierClosure, padicFourierDuality,
    HarmonicAnalysis.padicFourierScaling, HarmonicAnalysis.padicAdditiveConductor,
    padicFourierNormalization⟩

end Langlands.LocalFactors
