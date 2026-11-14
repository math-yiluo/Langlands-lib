import Langlands.Representation.RankinSelberg.RankOneExtensionAnalyticData
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionCharacter
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionTransport
/-! Concrete section, tensor and matrix data for the early JPSS Lemma 5.5 argument. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionEval rankOneExtensionLowerToUpperEquiv rankOneExtensionWhittakerContraction rankOneWhittakerType
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uW

section Tensor


end Tensor

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] (t : ℕ)
  (χ : Quasicharacter F)
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)

/-- Actual canonical normalized lower induction of `(σ, χLift)`. -/
abbrev rankOneExtensionLowerModel :=
  rankOneExtensionLowerInduced F t (rankOneExtensionCharacter.{uF, uW} F χ) σ

/-- Actual smooth covariant functions carrying the lower induced representation. -/
abbrev rankOneExtensionLowerSection :=
  letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (1 + (t + 1))
  (rankOneExtensionLowerModel F t χ σ).asModule

/-- Evaluate an actual lower induced section in its inducing tensor space. -/
def rankOneExtensionLowerSectionEval
    (f : rankOneExtensionLowerSection F t χ σ)
    (g : Langlands.GeneralLinear (1 + (t + 1)) F) :
    rankOneExtensionLowerTensor (W := W) := by
  letI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (1 + (t + 1))
  exact Induction.eval _ _ f g

/-- The contraction supplied by an inverse-character Whittaker functional on `σ`. -/
def rankOneExtensionWhittakerContraction
    (ψ : UnitaryAdditiveCharacter F)
    (ℓ : Whittaker.glInverseFunctionals ψ t σ) :
    rankOneExtensionLowerTensor (W := W) →ₗ[ℂ] ℂ :=
  rankOneExtensionTensorContraction ℓ.val

/-- The scalar coefficient of a section, for the specified inverse functional. -/
def rankOneExtensionLowerSectionCoefficient
    (ψ : UnitaryAdditiveCharacter F)
    (ℓ : Whittaker.glInverseFunctionals ψ t σ)
    (f : rankOneExtensionLowerSection F t χ σ)
    (g : Langlands.GeneralLinear (1 + (t + 1)) F) : ℂ :=
  rankOneExtensionWhittakerContraction F t σ ψ ℓ
    (rankOneExtensionLowerSectionEval F t χ σ f g)

end Padic

section Coordinates


end Coordinates

end Langlands.AllField.RankinSelberg
