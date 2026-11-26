import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOppositeLevelSetMeasureBoundProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalUnipotentWeightLevelReduction

/-! # Waldspurger II.4.2 on the actual opposite radical -/

universe u

namespace Langlands.HarishChandraSchwartz

/-- Weighted integrability for every actual opposite standard unipotent radical. -/
theorem rationalUnipotentWeightIntegrability : RationalUnipotentWeightIntegrabilityStatement.{u} :=
  rationalUnipotentWeightIntegrability_of_levelStatements rationalOppositeModulusLevelData
    rationalOppositeLevelSetMeasureBound

end Langlands.HarishChandraSchwartz
