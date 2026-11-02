import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualFactors
import Langlands.Representation.RankinSelberg.TwoBlockDominantGammaAlgebra
import Langlands.Representation.RankinSelberg.TwoBlockDominantGammaDuality
import Langlands.Representation.RankinSelberg.TwoBlockDominantCentralScalar
import Langlands.Representation.RankinSelberg.ModelMinusOneScalar

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  Polynomial TwoBlockJacquet LocalFactor TwoBlockLowerUnipotentQuotient
open scoped NNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance equalGammaProductTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance equalGammaProductValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance equalGammaProductLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance equalGammaProductT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance equalGammaProductMeasurable : MeasurableSpace F.Carrier := borel _
local instance equalGammaProductBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance equalGammaProductGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance equalGammaProductGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalGammaProductUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance equalGammaProductUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalGammaProductQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance equalGammaProductQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local instance equalGammaProductReverseAdd : ∀ i : Fin 2, AddCommGroup (W i.rev) :=
  fun i => hadd i.rev
local instance equalGammaProductReverseModule : ∀ i : Fin 2, Module ℂ (W i.rev) :=
  fun i => hmod i.rev

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V)
  (lambda : glFunctionals ψ t π)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))

/-- Complete gamma certificates for the two original blocks and their product
for the actual ordinary lower induction. -/
def EqualTwoBlockSymmetricGammaProduct : Prop :=
  ∃ G₁ G₂ : RationalFunctions,
    IsPadicSymmetricGammaFactor F ψ ν.val π (σ 0) G₁ ∧
    IsPadicSymmetricGammaFactor F ψ ν.val π (σ 1) G₂ ∧
    IsPadicSymmetricGammaFactor F ψ ν.val π (inducedRep F h σ) (G₁ * G₂)

set_option maxHeartbeats 1600000 in
/-- The retained actual rational comparison identifies a certified induced
factor with the product of complete certified block factors. -/
theorem equalTwoBlockSymmetricGammaProduct_of_rationalComparison
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hσtype : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hlambda : lambda.val ≠ 0) (hell : ∀ i, (ell i).val ≠ 0)
    (hσ : ∀ i, IsSmooth (σ i))
    (J : glInverseFunctionals ψ t (inducedRep F h σ))
    (hJ0 : J.val ≠ 0)
    (hJ : ∀ (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier),
      J.val (inducedRep F h σ g f) =
        jacquetFunction ψ (fun i => (ell i).val)
          (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f g)
    (μN : Measure (LeftUnipotentQuotient t F.Carrier))
    (μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
    (μB : Measure (LeftUnipotentQuotient (m 1) F.Carrier))
    (hμN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μN)
    (hμA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) μA)
    (hμB : IsCompatible (upperUnipotent (m 1 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 1)) (unipotentHaar F.Carrier (m 1)) μB)
    (hRational : EqualTwoBlockRationalComparison F h ψ ν π lambda σ ell hσ J μN μA μB) :
    EqualTwoBlockSymmetricGammaProduct F h ψ ν π σ := by
  let := unipotentHaar_isMulRightInvariant F.Carrier t
  let := unipotentHaar_isMulRightInvariant F.Carrier (m 0)
  let := unipotentHaar_isMulRightInvariant F.Carrier (m 1)
  let q := equalResidueCardinalityUnit F
  have hq := F.canonicalTopologicalData.residueCardinality_gt_one
  have hδ : (q⁻¹ : ℂˣ) = LocalFactor.residueReflection F := by
    apply Units.ext
    simp only [Units.val_inv_eq_inv_val, q, coe_equalResidueCardinalityUnit,
      LocalFactor.coe_residueReflection]
  have hδval : (↑(q⁻¹) : ℂ) = (qF : ℂ)⁻¹ := by
    simp only [Units.val_inv_eq_inv_val, q, coe_equalResidueCardinalityUnit]
  obtain ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D,
    hcert₁, hcert₂, hcompare, -, -⟩ := hRational
  have hfirst := EqualFirstBlockFactorCertificate.symmetricFactors F h ψ ν π lambda σ
    hπ hσtype hlambda ell (hell 0) hμA hcert₁
  have hπD := isOfWhittakerType_firstDual ψ π hπ
  have hσD := reversedDualBlocks_whittakerType F σ ψ hσtype
  have hsecond := EqualFirstBlockFactorCertificate.symmetricFactors F (reverse_sum h)
    (ψ.scale (-1)) (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
    (firstDualFunctional ψ π lambda)
    (fun i : Fin 2 => inverseTransposePullback (σ i.rev)) hπD hσD
    (firstDualFunctional_ne_zero ψ π hlambda)
    (fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev))
    (secondDualFunctional_ne_zero ψ (σ (0 : Fin 2).rev) (hell (0 : Fin 2).rev))
    hμB hcert₂
  have hG₁ : IsPadicSymmetricGammaFactor F ψ ν.val π (σ 0)
      (rationalGammaExpression q⁻¹ c₁ d₁ P₁ P₁D) := by
    rw [hδ]
    exact hfirst.2.2.2
  have hGD₂ : IsPadicSymmetricGammaFactor F (ψ.scale (-1)) ν.val
      (inverseTransposePullback π) (inverseTransposePullback (σ 1))
      (rationalGammaExpression q⁻¹ c₂ d₂ P₂D P₂) := by
    rw [hδ]
    exact hsecond.2.2.2
  have hsum : (m 0 + 1) + (m 1 + 1) = t + 1 := by
    simpa only [Fin.sum_univ_two] using h
  have hm₁ : m 1 < t := by omega
  let g₂ := padicSymmetricGammaFactorOfWhittakerType F ψ ν.val π (σ 1)
    (whittakerTypeGammaConstructionInput p F ψ ν t (m 1) V (W 1)
      π (σ 1) hπ (hσtype 1))
  have hG₂Eq := ((isPairGammaFactor_of_lt hm₁).mp
    ((isPadicSymmetricGammaFactor_of_le hm₁.le).mp g₂.property)).2.2.2
      μB hμB lambda (ell 1) hlambda (hell 1)
  have hGD₂Eq := ((isPairGammaFactor_of_lt hm₁).mp
    ((isPadicSymmetricGammaFactor_of_le hm₁.le).mp hGD₂)).2.2.2
      μB hμB (firstDualFunctional ψ π lambda) (secondDualFunctional ψ (σ 1) (ell 1))
      (firstDualFunctional_ne_zero ψ π hlambda)
      (secondDualFunctional_ne_zero ψ (σ 1) (hell 1))
  have hrec := unequalRankGammaEquation_reflection_mul hq hδval (hell 1) hG₂Eq hGD₂Eq
  obtain ⟨η₂, hη₂⟩ := exists_modelMinusOneScalar (σ 1)
    ((isOfWhittakerType_standard_iff_inverse ψ (σ 1)).mp (hσtype 1))
  have hη₂D := hasModelMinusOneScalar_secondDual ψ (σ 1) (ell 1) (hη₂ (ell 1))
  have hη₂eq : η₂ = ζ₂ := hη₂D.unique
    (secondDualFunctional_ne_zero ψ (σ 1) (hell 1)) hcert₂.2.1
  have hζ₂ : HasModelMinusOneScalar (σ 1) (ell 1) ζ₂ := by
    rw [← hη₂eq]
    exact hη₂ (ell 1)
  let ζblocks : Fin 2 → ℂˣ := ![ζ₁, ζ₂]
  have hζblocks : ∀ i, HasModelMinusOneScalar (σ i) (ell i) (ζblocks i) := by
    intro i
    fin_cases i
    · exact hcert₁.2.1
    · exact hζ₂
  have hζInd : HasModelMinusOneScalar (inducedRep F h σ) J (ζ₁ * ζ₂) := by
    simpa only [Fin.prod_univ_two, ζblocks, Matrix.cons_val_zero, Matrix.cons_val_one]
      using hasModelMinusOneScalar_of_jacquetRealization F h ψ σ ell ζblocks hζblocks
        (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) J hJ
  have hP₁D : P₁D ≠ 0 :=
    (hcert₁.2.2 0 (m 1) (by omega)).2.polynomial_ne_zero
  have hP₂ : P₂ ≠ 0 :=
    (hcert₂.2.2 0 (m 0) (by change t = m 1 + (0 + m 0 + 1); omega)).2.polynomial_ne_zero
  have hP₂D : P₂D ≠ 0 :=
    (hcert₂.2.2 0 (m 0) (by change t = m 1 + (0 + m 0 + 1); omega)).1.polynomial_ne_zero
  have hIndInv := lowerInduced_inverseWhittakerType F h ψ σ hσtype
  have hInd := (isOfWhittakerType_standard_iff_inverse ψ (inducedRep F h σ)).mpr hIndInv
  let g := padicSymmetricGammaFactorOfWhittakerType F ψ ν.val π (inducedRep F h σ)
    (whittakerTypeGammaConstructionInput p F ψ ν t t V (Sections F h σ)
      π (inducedRep F h σ) hπ hInd)
  have hEq := (isPairGammaFactor_self.mp
    ((isPadicSymmetricGammaFactor_of_le (le_refl t)).mp g.property)).2.2.2
      μN hμN lambda J hlambda hJ0
  obtain ⟨ζ, hζ, ⟨R₀, ⟨U, U', Φ, hR₀⟩, hR₀0⟩, hFE⟩ := hEq
  obtain ⟨f, rfl⟩ := modelMap_surjective (inducedRep F h σ) J U'
  obtain ⟨Φhat, R₁, RD₁, hpair, hR₁, hRD₁, hGamma⟩ :=
    hFE U (modelMap (inducedRep F h σ) J f) Φ
  obtain ⟨R₂, RD₂, hR₂, hRD₂, hclear⟩ := hcompare f U Φ Φhat hpair
  have hRD₂' : HasRationalContinuation qF
      (dualEqualRankModelIntegral ψ abv μN π (inducedRep F h σ) lambda J U
        (modelMap (inducedRep F h σ) J f) Φhat) RD₂ := by
    rw [transportedSecondDualFunctional_coefficient] at hRD₂
    exact hRD₂
  have hR₁₂ : R₁ = R₂ := hR₁.unique hq hR₂
  have hRD₁₂ : RD₁ = RD₂ := hRD₁.unique hq hRD₂'
  have hR₂0 : R₂ ≠ 0 := by rwa [← hR₀.unique hq hR₂]
  have hζeq : ζ = ζ₁ * ζ₂ := hζ.unique hJ0 hζInd
  have hactual := (RationalGammaComparison.gammaFunctionalEquation_iff_rational_identity
    hq hδval).mp hGamma
  rw [hR₁₂, hRD₁₂, hζeq] at hactual
  have hproduct := reflectedComparison_gammaProduct q ζ₁ c₁ d₁ ζ₂ c₂ d₂ t
    (hζ₂.sq_eq_one (hell 1)) hP₁D hP₂ hP₂D hrec hclear
  have hC : RatFunc.C (((ζ₁ * ζ₂ : ℂˣ) : ℂ) ^ t) ≠ 0 :=
    (_root_.map_ne_zero RatFunc.C).mpr (pow_ne_zero t (ζ₁ * ζ₂).ne_zero)
  have hg : (g.val : RationalFunctions) =
      rationalGammaExpression q⁻¹ c₁ d₁ P₁ P₁D * (g₂.val : RationalFunctions) :=
    mul_right_cancel₀ hR₂0 (mul_left_cancel₀ hC (hactual.symm.trans hproduct))
  exact ⟨_, _, hG₁, g₂.property, by rw [← hg]; exact g.property⟩

end Langlands.RankinSelberg.DominantRankTransport
