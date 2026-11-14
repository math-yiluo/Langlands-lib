import Langlands.Representation.RankinSelberg.RankOneExtensionLowerJacquetFunctionalProof
import Langlands.AllField.Group.GL.UpperUnipotentCompactContainmentProof
import Langlands.AllField.HarmonicAnalysis.PadicRowFourierEquivarianceProof
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionLowerCovariance
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionLowerJacquetFunctionalStatement
/-! # The absolute-domain lower Jacquet functional of the rank-one extension -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement RankOneExtensionLowerJacquetFunctionalStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerJacquetFunctional rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionCoefficient_lowerBlock_mul rankOneExtensionLowerSectionCoefficient_unipotentBlock_mul rankOneExtensionLowerSectionEval rankOneExtensionLowerShape_leviModulus rankOneExtensionLowerToUpperEquiv rankOneExtensionLowerTranslate rankOneExtensionStableIntegrand rankOneExtensionStableIntegrandMap rankOneExtensionStableIntegrandMap_apply rankOneExtensionStableIntegrand_apply rankOneExtensionStableIntegrand_translate rankOneExtensionStableIntegrand_unipotent_mul rankOneExtensionTensorContraction_comp_unipotent rankOneExtensionWhittakerContraction rankOneWhittakerType
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open scoped Matrix NNReal

universe uF uW

section Algebra


end Algebra

section Measure


end Measure

section Covariance

variable {F : Type uF} [Field F]
  {W : Type uW} [AddCommGroup W] [Module ℂ W] {t : ℕ}

/-- Contracting with `ℓ ∘ σ(u)` multiplies the contraction with `ℓ` by `θ_t(u)`. -/
theorem rankOneExtensionTensorContraction_comp_unipotent [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W}
    {ψ : UnitaryAdditiveCharacter F}
    (ℓ : Whittaker.glInverseFunctionals ψ t σ)
    (u : upperUnipotent (t + 1) F) (T : rankOneExtensionLowerTensor (W := W)) :
    rankOneExtensionTensorContraction (ℓ.val ∘ₗ σ u.val) T =
      (Whittaker.inverseStandardCharacter ψ t u : ℂ) *
        rankOneExtensionTensorContraction ℓ.val T := by
  refine piTensorProduct_comp_apply_eq_mul LinearMap.id _ _ _ (fun v => ?_) T
  rw [LinearMap.id_apply]
  erw [rankOneExtensionTensorContraction_tprod, rankOneExtensionTensorContraction_tprod]
  change ℓ.val (σ u.val (v 0)) * _ = _ * (ℓ.val (v 0) * _)
  rw [ℓ.property u (v 0), mul_assoc]

/-- The lower block `B(u, 0, 1)` with `u` upper unipotent multiplies the scalar coefficient
by `θ_t(u)`. -/
theorem rankOneExtensionLowerSectionCoefficient_unipotentBlock_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {χ : Quasicharacter F}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W}
    {ψ : UnitaryAdditiveCharacter F}
    (ℓ : Whittaker.glInverseFunctionals ψ t σ)
    (f : rankOneExtensionLowerSection F t χ σ) (u : upperUnipotent (t + 1) F)
    (g : Langlands.GeneralLinear (1 + (t + 1)) F) :
    rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f
        (rankOneExtensionLowerBlock t u.val 0 1 * g) =
      (Whittaker.inverseStandardCharacter ψ t u : ℂ) *
        rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ f g := by
  have hdet : (⟨⟩ : LocalFieldData F).determinantNorm (t + 1) u.val = 1 := by
    change (⟨⟩ : LocalFieldData F).normalizedAbsUnits (GeneralLinear.determinant u.val) = 1
    rw [show GeneralLinear.determinant u.val = 1 from Units.ext (unipotent_det u), map_one]
  rw [rankOneExtensionLowerSectionCoefficient_lowerBlock_mul, hdet, map_one, one_pow, div_one,
    map_one, Units.val_one, Units.val_one, NNReal.sqrt_one, NNReal.coe_one, Complex.ofReal_one,
    inv_one, one_mul, one_mul]
  exact rankOneExtensionTensorContraction_comp_unipotent ℓ u _

/-- Left translation of the ambient element by `n ∈ N` multiplies the integrand by
`θ(n)` and substitutes `y ↦ α⁻¹ (y + β)`. -/
theorem rankOneExtensionStableIntegrand_unipotent_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    {χ : Quasicharacter F}
    {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W}
    {ψ : UnitaryAdditiveCharacter F}
    (ℓ : Whittaker.glInverseFunctionals ψ t σ)
    (f : rankOneExtensionLowerSection F t χ σ) (n : upperUnipotent (1 + (t + 1)) F)
    (g : Langlands.GeneralLinear (1 + (t + 1)) F) (y : Fin (t + 1) → F) :
    rankOneExtensionStableIntegrand F t χ σ ψ ℓ f (n.val * g) y =
      (Whittaker.inverseStandardCharacter ψ (1 + t) n : ℂ) *
        rankOneExtensionStableIntegrand F t χ σ ψ ℓ f g (rankOneExtensionUnipotentShift n y) := by
  have hψ (b : F) : ψ.complex b ≠ 0 := by
    intro h
    have h' := AddChar.map_add_eq_mul ψ.complex b (-b)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h'
    exact one_ne_zero h'
  rw [rankOneExtensionStableIntegrand_apply, rankOneExtensionStableIntegrand_apply, ← mul_assoc,
    rankOneExtensionUpperCell_mul_unipotent, mul_assoc,
    rankOneExtensionLowerSectionCoefficient_unipotentBlock_mul ℓ f
      ⟨_, rankOneExtensionUnipotentHead_mem n⟩,
    rankOneExtension_inverseStandardCharacter, rankOneExtensionUnipotentShift_last,
    AddChar.map_add_eq_mul]
  have hβ := hψ (rankOneExtensionUnipotentColumn n (Fin.last t))
  field_simp

end Covariance

section Extension


end Extension

/-- The absolute-domain lower Jacquet functional: the integral functional on the subspace
where the integrand at the identity is integrable, extended to the whole lower induction. -/
theorem rankOneExtensionLowerJacquetFunctional :
    RankOneExtensionLowerJacquetFunctionalStatement.{uF, uW} := by
  intro F _ _ _ _ W _ _ t χ σ ψ ℓ ν
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let := T.fieldT2
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := T.generalLinearTopologicalGroup (1 + t + 1)
  let := T.upperUnipotentNonarchimedean (1 + t + 1)
  have hχ (a : F) (ha : a ≠ 0) :
      ν.val.measure.map (fun x => a * x) = (T.normalizedAbsHom a)⁻¹ • ν.val.measure :=
    padicScalarHaarScaling F T ν.val.measure (Units.mk0 a ha)
  let I := rankOneExtensionStableIntegrandMap F t χ σ ψ ℓ 1
  have hI (h : Langlands.GeneralLinear (1 + (t + 1)) F)
      (f : rankOneExtensionLowerSection F t χ σ) :
      I (rankOneExtensionLowerTranslate F t χ σ h f) =
        rankOneExtensionStableIntegrand F t χ σ ψ ℓ f h :=
    (rankOneExtensionStableIntegrand_translate F t χ σ ψ ℓ h 1 f).trans (by rw [one_mul])
  obtain ⟨L, hL⟩ := exists_functional_eq_integral_of_covariant _ _ _
    (upperUnipotent_isLimitOfCompactSubgroups F T (1 + t + 1))
    (isLocallyConstant_of_continuous_complex_character _
      (Whittaker.inverseStandardCharacterContinuous ψ (1 + t)).continuous)
    (T.isSmooth_normalizedOppositeParabolicInduced _ _)
    I (rowMeasure ν.val (t + 1)) rankOneExtensionUnipotentShift
    (measurePreserving_rankOneExtensionUnipotentShift T.normalizedAbsHom ν.val hχ)
    measurableEmbedding_rankOneExtensionUnipotentShift
    (fun n f => by
      funext y
      have h := rankOneExtensionStableIntegrand_unipotent_mul ℓ f n 1 y
      rw [mul_one] at h
      exact (congrFun (hI n.val f) y).trans h)
  refine ⟨L, fun f g hfg => ?_⟩
  have h := hL (rankOneExtensionLowerTranslate F t χ σ g f)
    ((congrArg (fun φ => Integrable φ (rowMeasure ν.val (t + 1))) (hI g f)).mpr hfg)
  refine h.trans ?_
  exact congrArg (fun φ => ∫ y, φ y ∂rowMeasure ν.val (t + 1)) (hI g f)

end Langlands.AllField.RankinSelberg
