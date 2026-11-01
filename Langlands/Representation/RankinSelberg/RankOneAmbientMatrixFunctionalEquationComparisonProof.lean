import Langlands.Representation.RankinSelberg.RankOneAmbientMatrixFunctionalEquationComparisonStatement
import Langlands.Representation.RankinSelberg.RankOneAmbientMatrixFunctionalEquationComparisonPositive
import Langlands.Representation.RankinSelberg.RankOneAmbientMatrixFunctionalEquationComparisonZeroPadic

/-! # Rank-one gamma comparison from ambient matrix data -/

namespace Langlands.RankinSelberg

universe uF uV uW

/-- The ambient normalized matrix functional equation gives the complete
symmetric rank-one gamma certificate for the original representation, in
every rank and with independent field and carrier universes. -/
theorem rankOneAmbientMatrixFunctionalEquationComparison :
    RankOneAmbientMatrixFunctionalEquationComparisonStatement.{uF, uV, uW} := by
  intro p _ F ψ ν hsd n V _ _ σ hσ ℓ hℓ W _ _ ρ hinc P PDual c a hData
  cases n with
  | zero =>
    exact rankOneAmbientMatrixFunctionalEquationComparison_zero
      F ψ ν σ hσ ℓ hℓ ρ hinc hData
  | succ m =>
    exact AmbientMatrixComparison.gammaFactor F ψ ν σ ℓ hsd hσ hℓ ρ hinc hData

end Langlands.RankinSelberg
