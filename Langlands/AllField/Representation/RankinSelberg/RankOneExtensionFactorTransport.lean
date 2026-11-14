import Langlands.Representation.RankinSelberg.RankOneExtensionFactorTransport
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionTransport
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerToUpper rankOneExtensionLowerToUpperEquiv rankOneExtensionSymmetricLPolynomial_iff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding functionalsCongr
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (t : ℕ)
  (χ : Representation ℂ (Langlands.GeneralLinear 1 F) (ULift.{uW} ℂ))
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
  (hχ : IsSmooth χ)
  (hσ : IsSmooth σ)

/-- Choose an actual intertwining equivalence to the exact upper induction.
This choice carries no prescribed formula on section evaluations. -/
def rankOneExtensionLowerToUpper :
    letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (1 + (t + 1))
    Representation.Equiv (rankOneExtensionLowerInduced F t χ σ)
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (rankOneExtensionUpperShape t)
        (Shahidi.pairFamily χ σ)) :=
  Classical.choice (rankOneExtensionLowerToUpperEquiv F t χ σ hχ hσ)

include hχ hσ

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Certified polynomials for the actual pair transport with the same measure. -/
theorem rankOneExtensionSymmetricLPolynomial_iff
    (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F;
      AdditiveHaarMeasure F)
    {r : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (P : ℂ[X]) :
    IsPadicSymmetricLPolynomial F ψ ν π (rankOneExtensionLowerInduced F t χ σ) P ↔
      IsPadicSymmetricLPolynomial F ψ ν π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (rankOneExtensionUpperShape t)
          (Shahidi.pairFamily χ σ)) P := by
  exact Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv (Representation.Equiv.refl π)
    (rankOneExtensionLowerToUpper F t χ σ hχ hσ)

end Langlands.AllField.RankinSelberg
