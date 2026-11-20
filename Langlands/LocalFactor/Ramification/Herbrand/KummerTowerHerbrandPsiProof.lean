import Langlands.LocalFactor.Ramification.Herbrand.KummerTowerUpperSupProof
import Langlands.LocalFactor.Ramification.Herbrand.KummerTruncationProof

namespace Langlands.Ramification.Kummer

universe u

/-- The relative inverse Herbrand function of each finite Kummer stage fixes
every index from `-1` through the first Kummer break. -/
theorem kummerTowerHerbrandPsi : KummerTowerHerbrandPsiStatement.{u} := by
  intro p _ F ϖ πs hπ n x hx_lower hx_upper
  have htop := kummerTowerUpperSup p F ϖ πs hπ n (kummerBreak F)
    (hx_lower.trans hx_upper) le_rfl
  exact herbrandPsiTruncation p F (kummerStage F πs n) (kummerBreak F)
    htop x hx_lower hx_upper

end Langlands.Ramification.Kummer
