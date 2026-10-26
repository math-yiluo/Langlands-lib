import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Analysis.Local.QuotientTopology

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV uW

/-- Continuity of the actual zero-row unequal-rank quotient integrand for smooth
coefficient models and a continuous real absolute value. The small rank is
`n + 1` and the large rank exceeds it by the positive gap `k + 1`. -/
def UnequalRankZeroRowIntegrandContinuousStatement (F : Type uF) [Field F]
    [TopologicalSpace F] [IsTopologicalRing F] (n k : ℕ) : Prop :=
  ∀ (abv : AbsoluteValue F ℝ), Continuous abv →
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
  ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
    IsSmooth π → IsSmooth σ →
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (ℓ : glFunctionals ψ (n + (0 + k + 1)) π) (ℓ' : glInverseFunctionals ψ n σ)
      (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule) (s : ℂ),
      Continuous (unequalRankIntegrand ψ abv 0 k f.val f'.val s 0)

end Langlands.RankinSelberg
