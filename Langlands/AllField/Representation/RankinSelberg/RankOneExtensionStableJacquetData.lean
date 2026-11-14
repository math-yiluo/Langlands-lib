import Langlands.Representation.RankinSelberg.RankOneExtensionStableJacquetData
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionAnalyticData
/-!
# Stabilized lower Jacquet data for the strict rank-one extension

JPSS (1983), Lemma (5.5), printed page 424, formula (1): the Whittaker functional
of the lower induction is the limit, over an exhaustion by compact open subgroups,
of truncated integrals of the scalar contraction of a section against the character.
This module defines the actual scalar integrand on the row coordinates of the upper
cell, its compact-open stable graph, the domain of sections where it stabilizes, the
linear stable value on that domain and a conditional extension. It asserts no
stabilization for any particular section.
-/

noncomputable section

open MeasureTheory

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionEval rankOneExtensionLowerToUpperEquiv rankOneExtensionLowerTranslate rankOneExtensionStableIntegrand rankOneExtensionStableIntegrandMap rankOneExtensionStableIntegrandMap_apply rankOneExtensionStableIntegrand_apply rankOneExtensionStableIntegrand_translate rankOneExtensionWhittakerContraction rankOneWhittakerType
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uW

section Row


end Row

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] (t : ℕ)
  (χ : Quasicharacter F)
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
  (ψ : UnitaryAdditiveCharacter F)
  (ℓ : Whittaker.glInverseFunctionals ψ t σ)

/-- The actual induced right action of `h` on the section carrier, transported through
`asModuleEquiv`. -/
def rankOneExtensionLowerTranslate (h : Langlands.GeneralLinear (1 + (t + 1)) F) :
    rankOneExtensionLowerSection F t χ σ →ₗ[ℂ] rankOneExtensionLowerSection F t χ σ :=
  (rankOneExtensionLowerModel F t χ σ).asModuleEquiv.symm.toLinearMap ∘ₗ
    rankOneExtensionLowerModel F t χ σ h ∘ₗ
      (rankOneExtensionLowerModel F t χ σ).asModuleEquiv.toLinearMap

/-- The scalar integrand `y ↦ ℓ(f(u(y) g)) ψ(y_last)` on the row coordinates of the
complementary upper cell, with the positive character. -/
def rankOneExtensionStableIntegrand (f : rankOneExtensionLowerSection F t χ σ)
    (g : Langlands.GeneralLinear (1 + (t + 1)) F)
    (y : Fin (t + 1) → F) : ℂ :=
  rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f (rankOneExtensionUpperCell t y * g) *
    ψ.complex (y (Fin.last t))

theorem rankOneExtensionStableIntegrand_apply (f : rankOneExtensionLowerSection F t χ σ)
    (g : Langlands.GeneralLinear (1 + (t + 1)) F) (y : Fin (t + 1) → F) :
    rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g y =
      rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f
          (rankOneExtensionUpperCell t y * g) *
        ψ.complex (y (Fin.last t)) :=
  rfl

/-- The integrand at a fixed ambient element, as a complex linear map of the section. -/
def rankOneExtensionStableIntegrandMap
    (g : Langlands.GeneralLinear (1 + (t + 1)) F) :
    rankOneExtensionLowerSection F t χ σ →ₗ[ℂ] (Fin (t + 1) → F) → ℂ where
  toFun f := rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g
  map_add' f f' := by
    funext y
    change rankOneExtensionWhittakerContraction F t σ ψ ℓ
        (rankOneExtensionLowerSectionEval F t χ σ f (rankOneExtensionUpperCell t y * g) +
          rankOneExtensionLowerSectionEval F t χ σ f' (rankOneExtensionUpperCell t y * g)) *
        _ = _
    rw [map_add, add_mul]
    rfl
  map_smul' c f := by
    funext y
    change rankOneExtensionWhittakerContraction F t σ ψ ℓ
        (c • rankOneExtensionLowerSectionEval F t χ σ f
          (rankOneExtensionUpperCell t y * g)) * _ = _
    rw [map_smul, smul_eq_mul, mul_assoc]
    rfl

@[simp] theorem rankOneExtensionStableIntegrandMap_apply
    (g : Langlands.GeneralLinear (1 + (t + 1)) F)
    (f : rankOneExtensionLowerSection F t χ σ) :
    rankOneExtensionStableIntegrandMap F t χ σ ψ ℓ g f =
      rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g :=
  rfl

/-- Translating the section by `h` under the actual induced right action replaces the
ambient element `g` by `g * h`. -/
theorem rankOneExtensionStableIntegrand_translate
    (h g : Langlands.GeneralLinear (1 + (t + 1)) F)
    (f : rankOneExtensionLowerSection F t χ σ) :
    rankOneExtensionStableIntegrand F t χ σ ψ ℓ (rankOneExtensionLowerTranslate F t χ σ h f) g =
      rankOneExtensionStableIntegrand F t χ σ ψ ℓ f (g * h) := by
  funext y
  change rankOneExtensionWhittakerContraction F t σ ψ ℓ
      (rankOneExtensionLowerSectionEval F t χ σ f (rankOneExtensionUpperCell t y * g * h)) *
      _ = _
  rw [mul_assoc]
  rfl









end Padic

end Langlands.AllField.RankinSelberg
