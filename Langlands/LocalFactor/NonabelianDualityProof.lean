import Langlands.LocalFactor.AbelianDualityFromAnalysis
import Langlands.LocalFactor.CommonClosureGenerationProof
import Langlands.LocalFactor.PadicAbelianLocalAnalysisProof

/-! # Dual functional equations for actual virtual local constants -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem

/-- Fixed-Haar and spectral duality for every supplied normalized system on
the actual continuous exact virtual groups. -/
theorem dualFunctionalEquation : DualFunctionalEquationStatement.{uF, uV} :=
  dualFunctionalEquation_of_generation_of_localAnalysis.{uF, uV}
    commonClosureDegreeZeroGeneration.{uF, uV}
    padicAbelianLocalAnalysis.{uF}

end Langlands.LocalFactor.NonabelianSystem
