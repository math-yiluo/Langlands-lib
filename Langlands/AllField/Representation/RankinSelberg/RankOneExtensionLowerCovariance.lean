import Langlands.Representation.RankinSelberg.RankOneExtensionLowerCovariance
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionStableJacquetData
/-!
# Lower-parabolic covariance of the rank-one extension sections

The lower block `B(m, x, a) = [m, 0; x, a]` lies in the opposite parabolic of the lower
shape `(t + 1, 1)`, with Levi part `(m, a)`. The scalar coefficient of an actual lower
induced section therefore satisfies
`c_f(B(m, x, a) g) = δ(m, a)^(-1/2) χ(a) · (ℓ ∘ σ(m) ⊗ id)(f(g))`, where
`δ(m, a) = |det m| / |a|^(t + 1)`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionCoefficient_lowerBlock_mul rankOneExtensionLowerSectionEval rankOneExtensionLowerShape_leviModulus rankOneExtensionLowerToUpperEquiv rankOneExtensionLowerTranslate rankOneExtensionStableIntegrand rankOneExtensionStableIntegrandMap rankOneExtensionStableIntegrandMap_apply rankOneExtensionStableIntegrand_apply rankOneExtensionStableIntegrand_translate rankOneExtensionWhittakerContraction rankOneWhittakerType
open Langlands.AllField.RankinSelberg

open Matrix
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open scoped NNReal

universe uF uW

section Algebra


end Algebra

section TensorExt

end TensorExt

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] (t : ℕ)
  (χ : Quasicharacter F)
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)

/-- The lower Levi modulus is `|det m| / |a| ^ (t + 1)`. -/
theorem rankOneExtensionLowerShape_leviModulus
    (L : (rankOneExtensionLowerShape t).Levi F) :
    (⟨⟩ : LocalFieldData F).leviModulus (rankOneExtensionLowerShape t) L =
      (⟨⟩ : LocalFieldData F).determinantNorm (t + 1) (L (rankOneExtensionLowerLargeBlock t)) /
        (⟨⟩ : LocalFieldData F).determinantNorm 1
          (L (rankOneExtensionLowerScalarBlock t)) ^ (t + 1) := by
  rw [Langlands.LocalFieldData.leviModulus_apply]
  simp only [Finset.prod_filter]
  erw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two]
  simp
  rfl

/-- The coefficient formula
`c_f(B(m, x, a) g) = δ(m, a)^(-1/2) χ(a) · (ℓ ∘ σ(m) ⊗ id)(f(g))`, with
`δ(m, a) = |det m| / |a| ^ (t + 1)`. -/
theorem rankOneExtensionLowerSectionCoefficient_lowerBlock_mul
    (ψ : UnitaryAdditiveCharacter F)
    (ℓ : Whittaker.glInverseFunctionals ψ t σ)
    (f : rankOneExtensionLowerSection F t χ σ)
    (m : Langlands.GeneralLinear (t + 1) F) (x : Fin (t + 1) → F)
    (a : Fˣ) (g : Langlands.GeneralLinear (1 + (t + 1)) F) :
    rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f
        (rankOneExtensionLowerBlock t m x a * g) =
      (((NNReal.sqrt (((⟨⟩ : LocalFieldData F).determinantNorm (t + 1) m /
          (⟨⟩ : LocalFieldData F).normalizedAbsUnits a ^ (t + 1) : ℝ≥0ˣ) : ℝ≥0) : ℝ) :
            ℂ))⁻¹ * ((χ a : ℂˣ) : ℂ) *
        rankOneExtensionTensorContraction (ℓ.val ∘ₗ σ m)
          (rankOneExtensionLowerSectionEval F t χ σ f g) := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (1 + (t + 1))
  let : ∀ i : Fin (rankOneExtensionLowerShape t).length,
      AddCommGroup (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
    Shahidi.pairCarrier.instAddCommGroup i.rev
  let : ∀ i : Fin (rankOneExtensionLowerShape t).length,
      Module ℂ (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
    Shahidi.pairCarrier.instModule ℂ i.rev
  set L := (rankOneExtensionLowerShape t).oppositeLeviProjection F
    (rankOneExtensionLowerBlockParabolic m x a) with hL
  have hLm : L (rankOneExtensionLowerLargeBlock t) = m :=
    oppositeLeviProjection_lowerBlock_large m x a
  have hLa : GeneralLinear.determinant (L (rankOneExtensionLowerScalarBlock t)) = a :=
    oppositeLeviProjection_lowerBlock_scalar_det m x a
  have hcov := (⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced_covariant _ _ f
    (rankOneExtensionLowerBlockParabolic m x a) g
  have key : ∀ T : rankOneExtensionLowerTensor (W := W),
      rankOneExtensionTensorContraction ℓ.val
        ((rankOneExtensionLowerShape t).blockTensor (V := rankOneExtensionLowerCarrier (W := W))
          (rankOneExtensionLowerFamily F t (rankOneExtensionCharacter.{uF, uW} F χ) σ) L T) =
        ((χ a : ℂˣ) : ℂ) * rankOneExtensionTensorContraction (ℓ.val ∘ₗ σ m) T := by
    refine piTensorProduct_comp_apply_eq_mul _ _ _ _ fun v => ?_
    erw [GeneralLinear.BlockShape.blockTensor_tprod]
    erw [rankOneExtensionTensorContraction_tprod, rankOneExtensionTensorContraction_tprod]
    change ℓ.val (σ (L (rankOneExtensionLowerLargeBlock t)) (v 0)) *
          (((χ (GeneralLinear.determinant (L (rankOneExtensionLowerScalarBlock t))) : ℂˣ) : ℂ) *
            (v 1 : ULift.{uW} ℂ).down) =
        ((χ a : ℂˣ) : ℂ) * (ℓ.val (σ m (v 0)) * (v 1 : ULift.{uW} ℂ).down)
    rw [hLm, hLa]
    ring
  have hδ : (⟨⟩ : LocalFieldData F).leviModulus (rankOneExtensionLowerShape t) L =
      (⟨⟩ : LocalFieldData F).determinantNorm (t + 1) m /
        (⟨⟩ : LocalFieldData F).normalizedAbsUnits a ^ (t + 1) := by
    rw [rankOneExtensionLowerShape_leviModulus, hLm]
    congr 2
    exact congrArg (⟨⟩ : LocalFieldData F).normalizedAbsUnits hLa
  change rankOneExtensionTensorContraction ℓ.val
      (Induction.eval _ _ f (rankOneExtensionLowerBlock t m x a * g)) = _
  erw [hcov]
  rw [map_smul, smul_eq_mul]
  erw [key]
  rw [hδ, mul_assoc]
  rfl

end Padic

end Langlands.AllField.RankinSelberg
