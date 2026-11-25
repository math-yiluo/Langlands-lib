import Langlands.LocalFactor.Ramification.Herbrand.KummerTowerUpperSupProof
import Langlands.LocalFactor.Ramification.Herbrand.TruncationGaloisQuotientProof

/-!
# Galois truncation quotients at finite Kummer stages

A proof of `Langlands.Ramification.Kummer.KummerStageGaloisQuotientStatement`: the transitivity
of the upper groups through the Kummer break on every finite stage (`kummerTowerUpperSup`) is
the hypothesis of the Galois truncation theorem (`truncationGaloisQuotient`) at the transitivity
index `kummerBreak F`. See the paired Markdown.
-/

namespace Langlands.Ramification.Kummer

universe u

/-- The inclusion of each finite Kummer stage `K_n = F(πs n)` induces filtered topological
Galois quotient isomorphisms `G_{K_n}/G_{K_n}^x ≃ G_F/G_F^x` for `-1 ≤ x ≤ p e/(p - 1)`. -/
theorem kummerStageGaloisQuotient : KummerStageGaloisQuotientStatement.{u} := by
  intro p _ F ϖ πs hπ n x hx hxbreak
  have htrans := kummerTowerUpperSup p F ϖ πs hπ n (kummerBreak F)
    (hx.trans hxbreak) le_rfl
  exact truncationGaloisQuotient p F (kummerStage F πs n) (kummerBreak F) htrans x hx hxbreak

end Langlands.Ramification.Kummer
