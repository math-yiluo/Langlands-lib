import Langlands.LocalFactor.Ramification.Herbrand.KummerTowerUpperSupProof
import Langlands.LocalFactor.Ramification.Herbrand.TruncationWeilQuotientProof

namespace Langlands.Ramification.Kummer

universe u

/-- The inclusion of each finite Kummer stage induces filtered topological Weil
quotient isomorphisms through the common Kummer break. -/
theorem kummerStageWeilQuotient : KummerStageWeilQuotientStatement.{u} := by
  intro p _ F ϖ πs hπ n x hx hxbreak
  have htrans := kummerTowerUpperSup p F ϖ πs hπ n (kummerBreak F)
    (hx.trans hxbreak) le_rfl
  exact truncationWeilQuotient p F (kummerStage F πs n) (kummerBreak F) htrans x hx hxbreak

end Langlands.Ramification.Kummer
