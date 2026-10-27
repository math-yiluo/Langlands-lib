import Langlands.Representation.RankinSelberg.EqualRankFunctionalEquationSwapStatement
import Langlands.Representation.RankinSelberg.EqualRankFactorSwapProof

/-! Equal-rank epsilon and gamma exchange, projected from the full factor exchange. -/

namespace Langlands.RankinSelberg

universe uF uV uW

/-- The epsilon and gamma certificate equivalences are the last two conjuncts of
the published equal-rank factor exchange `equalRankFactorSwap`. -/
theorem equalRankFunctionalEquationSwap :
    EqualRankFunctionalEquationSwapStatement.{uF, uV, uW} := by
  intro p hp F ψ ν n V hV hMV W hW hMW π σ hπ hσ
  exact (equalRankFactorSwap.{uF, uV, uW} p F ψ ν n π σ hπ hσ).2

end Langlands.RankinSelberg
