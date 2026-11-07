import Langlands.LocalFactor.CommonClosureGenerationProof
import Langlands.LocalFactor.CommonClosureRankOneSpectral
import Langlands.LocalFactor.CommonClosureSpectralGenerationReduction

/-!
# Analyticity of ordinary common-closure spectral local constants

The rank-one analyticity of every supplied system and the generation reduction
give analyticity of every ordinary spectral value.
-/

universe uF uV

namespace Langlands.LocalFactor.CommonClosureSpectralAnalytic

open CommonClosure CommonClosureSpectral NonabelianSystem

/-- Every supplied system has analytic spectral values on rank-one classes. -/
theorem rankOneAnalytic {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    {e : ReciprocityFamily F} {ε : Assignment.{uF, uV} F} (hε : IsSystem F e ε) :
    RankOneAnalytic ε :=
  fun L ψ μ χ s => weilCharacter_analyticAt F e L ε hε ψ μ χ s

/-- Degree-zero generation over every base field gives the analyticity
statement. -/
theorem spectralAnalytic_of_generation
    (hgen : CommonClosureDegreeZeroGenerationStatement.{uF, uV}) :
    CommonClosureSpectralAnalyticStatement.{uF, uV} :=
  fun {p} _ F _ _ hε E ψ μ x s =>
    analyticAt_of_generation (hgen p F) hε (rankOneAnalytic hε) E ψ μ x s

end Langlands.LocalFactor.CommonClosureSpectralAnalytic

namespace Langlands.LocalFactor

/-- Ordinary spectral local constants of every supplied common-closure system
are analytic over every finite intermediate field and exact virtual class. -/
theorem commonClosureSpectralAnalytic :
    CommonClosureSpectralAnalyticStatement.{uF, uV} :=
  CommonClosureSpectralAnalytic.spectralAnalytic_of_generation
    commonClosureDegreeZeroGeneration.{uF, uV}

end Langlands.LocalFactor
