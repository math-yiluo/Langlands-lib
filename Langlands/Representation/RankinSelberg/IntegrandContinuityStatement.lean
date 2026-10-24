import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Analysis.Local.QuotientTopology

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV uW

/-- Continuity of the actual equal-rank quotient integrand for smooth
coefficient models and a continuous real absolute value. -/
def EqualRankIntegrandContinuousStatement (F : Type uF) [Field F]
    [TopologicalSpace F] [IsTopologicalRing F] (n : ℕ) : Prop :=
  ∀ (abv : AbsoluteValue F ℝ), Continuous abv →
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
  ∀ (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
    IsSmooth π → IsSmooth σ →
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
      (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule)
      (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ),
      Continuous (equalRankIntegrand ψ abv f.val f'.val Φ s)

end Langlands.RankinSelberg
