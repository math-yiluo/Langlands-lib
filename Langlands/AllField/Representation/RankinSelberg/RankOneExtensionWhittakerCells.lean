import Langlands.Representation.RankinSelberg.RankOneExtensionWhittakerCells
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionLowerCovariance
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionSpanTransfer
/-!
# Whittaker characters on the rank-one extension cells

For a Whittaker function `W` of rank `(1 + (t + 1)) + k`, read through the standard rank
inclusion `ι = diag(·, I_(k+1))`:
`W(ι(u(y) z)) = ψ(y_t) W(ι z)` and `W(ι(B(n, 0, 1) z)) = θ(n) W(ι z)` for `n ∈ N_(t+1)`.
The scalar coefficient of a lower induced section transforms by the inverse character:
`c_f(B(n, 0, 1) z) = θ(n)⁻¹ c_f(z)`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement RankOneExtensionSpanComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionCoefficient_lowerBlock_mul rankOneExtensionLowerSectionCoefficient_unipotent_mul rankOneExtensionLowerSectionEval rankOneExtensionLowerShape_leviModulus rankOneExtensionLowerToUpperEquiv rankOneExtensionLowerTranslate rankOneExtensionSpanComparison_of_pointwise rankOneExtensionStableIntegrand rankOneExtensionStableIntegrandMap rankOneExtensionStableIntegrandMap_apply rankOneExtensionStableIntegrand_apply rankOneExtensionStableIntegrand_translate rankOneExtensionWhittakerContraction rankOneWhittakerType
open Langlands.AllField.RankinSelberg

open Matrix
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding functionalsCongr
open scoped NNReal

universe uF uW

section Entries


end Entries

section Whittaker


end Whittaker

section Coefficient

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (t : ℕ)
  (χ : Quasicharacter F)
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)

/-- `c_f(B(n, 0, 1) z) = θ(n)⁻¹ c_f(z)` for `n ∈ N_(t+1)`. -/
theorem rankOneExtensionLowerSectionCoefficient_unipotent_mul
    (ψ : UnitaryAdditiveCharacter F)
    (ℓ : Whittaker.glInverseFunctionals ψ t σ)
    (f : rankOneExtensionLowerSection F t χ σ) (n : upperUnipotent (t + 1) F)
    (z : Langlands.GeneralLinear (1 + (t + 1)) F) :
    rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f
        (rankOneExtensionLowerBlock t n.val 0 1 * z) =
      ((inverseStandardCharacter ψ t n : ℂˣ) : ℂ) *
        rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f z := by
  rw [rankOneExtensionLowerSectionCoefficient_lowerBlock_mul]
  have hdet : (⟨⟩ : LocalFieldData F).determinantNorm (t + 1) n.val = 1 := by
    apply Units.ext
    rw [Langlands.LocalFieldData.determinantNorm, MonoidHom.comp_apply]
    have : GeneralLinear.determinant n.val = 1 := Units.ext (unipotent_det n)
    rw [this, map_one]
  have hℓ : ℓ.val ∘ₗ σ n.val = ((inverseStandardCharacter ψ t n : ℂˣ) : ℂ) • ℓ.val := by
    apply LinearMap.ext
    intro w
    exact ℓ.property n w
  rw [hdet, map_one, one_pow, div_one, Units.val_one, NNReal.sqrt_one, NNReal.coe_one,
    Complex.ofReal_one, inv_one, one_mul, map_one, Units.val_one, one_mul, hℓ,
    rankOneExtensionTensorContraction_smul, LinearMap.smul_apply, smul_eq_mul]
  rfl

end Coefficient

end Langlands.AllField.RankinSelberg
