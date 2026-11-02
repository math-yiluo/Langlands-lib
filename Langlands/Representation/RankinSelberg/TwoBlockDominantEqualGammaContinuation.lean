import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualGammaFamilies
import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualGammaBound
import Langlands.Representation.RankinSelberg.AdjacentRankFixedGamma
import Langlands.Representation.RankinSelberg.UnramifiedTwistGammaProof

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  ParameterSpecialization AdjacentGammaContinuation LocalFactor Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance equalGammaContinuationTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance equalGammaContinuationValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance equalGammaContinuationLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance equalGammaContinuationT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance equalGammaContinuationMeasurable : MeasurableSpace F.Carrier := borel _
local instance equalGammaContinuationBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance equalGammaContinuationGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance equalGammaContinuationGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalGammaContinuationUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance equalGammaContinuationUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalGammaContinuationQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance equalGammaContinuationQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue T

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))

/-- Complete certificates for the fixed opposite spectral gamma product. -/
def EqualOppositeRealRayGammaCertificates
    (G₀ G₁ : RationalFunctions) (Cbound : ℝ) : Prop :=
  ∀ u : ℝ, Cbound < u →
    IsPadicSymmetricGammaFactor F ψ ν.val π
      (complexOppositeTwistInduced F m h σ (u : ℂ))
      (oppositeSpectralGammaProduct qF F.canonicalTopologicalData.residueCardinality_gt_one G₀ G₁ (u : ℂ))

/-- Unramified transport and complete-certificate uniqueness identify the
large-real-twist witnesses with the two fixed original block factors. -/
theorem exists_equalOppositeRealRayGammaCertificates
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (G₀ G₁ : RationalFunctions)
    (hG₀ : IsPadicSymmetricGammaFactor F ψ ν.val π (σ 0) G₀)
    (hG₁ : IsPadicSymmetricGammaFactor F ψ ν.val π (σ 1) G₁) :
    ∃ Cbound : ℝ, EqualOppositeRealRayGammaCertificates F h ψ ν π σ G₀ G₁ Cbound := by
  obtain ⟨Cbound, hC⟩ := exists_equalTwoBlockSymmetricGammaProduct F h ψ ν π σ hπ hσ
  refine ⟨Cbound, fun u hu => ?_⟩
  obtain ⟨H₀, H₁, hH₀, hH₁, hH⟩ := hC u hu
  have hG₀' := Padic.symmetricGammaFactor_determinantComplexPower_of_transport
    F unramifiedTwistGamma ψ ν π (σ 0) (-(u : ℂ)) G₀ hG₀
  have hG₁' := Padic.symmetricGammaFactor_determinantComplexPower_of_transport
    F unramifiedTwistGamma ψ ν π (σ 1) (u : ℂ) G₁ hG₁
  have he0 : H₀ = rationalRescale
      (spectralShiftUnit qF F.canonicalTopologicalData.residueCardinality_gt_one (-(u : ℂ))) G₀ :=
    hH₀.unique hG₀'
  have he1 : H₁ = rationalRescale
      (spectralShiftUnit qF F.canonicalTopologicalData.residueCardinality_gt_one (u : ℂ)) G₁ :=
    hH₁.unique hG₁'
  simpa only [he0, he1, oppositeSpectralGammaProduct] using hH

section ActualContinuation

variable [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
  (μ : Measure (LeftUnipotentQuotient t F.Carrier)) [IsFiniteMeasureOnCompacts μ]
  (hμ : IsCompatible (upperUnipotent (t + 1) F.Carrier)
    (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μ)
  (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
  (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
  (lambda : glFunctionals ψ t π) (hlambda : lambda.val ≠ 0)
  (ell : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
  (hell : ell.val ≠ 0)
  (f : (coefficientModel π lambda).toSubmodule)
  (f' : (coefficientModel (TwoBlockJacquet.inducedRep F h σ) ell).toSubmodule)
  (Φ Φhat : SchwartzBruhat (Fin (t + 1) → F.Carrier))
  (hΦ : IsRowFourierPair ψ ν.val Φ Φhat)
  (ζ : ℂˣ) (hζ : HasModelMinusOneScalar (TwoBlockJacquet.inducedRep F h σ) ell ζ)
  (G₀ G₁ : RationalFunctions) (P₀ P₁ : Polynomial ℂ) (hP : P₀ * P₁ ≠ 0)
  (Cbound : ℝ)
  (hclear : EqualOppositeRealRayClearing F h ψ π σ μ lambda P₀ P₁ Cbound)
  (hgamma : EqualOppositeRealRayGammaCertificates F h ψ ν π σ G₀ G₁ Cbound)

include hμ hπ hσ hlambda hell hΦ hζ hP hclear hgamma

/-- Continue the sign-absorbed actual gamma equations and restore the
original model scalar at zero. -/
theorem equalTwoBlock_gamma_at_zero :
    ∃ R Rd : RationalFunctions,
      HasRationalContinuation qF
        (equalRankModelIntegral ψ abv μ π (TwoBlockJacquet.inducedRep F h σ)
          lambda ell f f' Φ) R ∧
      HasRationalContinuation qF
        (dualEqualRankModelIntegral ψ abv μ π (TwoBlockJacquet.inducedRep F h σ)
          lambda ell f f' Φhat) Rd ∧
      GammaFunctionalEquation qF ζ t (G₀ * G₁) R Rd := by
  classical
  obtain ⟨U, hU0, hcoeff, ⟨K, hKo, hKc, hK⟩, hUa⟩ :=
    exists_oppositeWhittakerFamily F m h σ ψ hσ ell hell f'
  obtain ⟨hae, hade⟩ := equalGammaSliceFamilies_entire F ψ U K hKo hKc hK hUa
    μ π hπ lambda f Φ Φhat
  let I := fun u s => equalRankIntegral ψ abv μ f.val
    (translateInverseWhittaker ψ (U u) ((-1) ^ t)) Φ s
  let Id := fun u s => equalRankIntegral (ψ.scale (-1)) abv μ
    (firstDualFunction ψ t f.val) (secondDualFunction ψ t (U u)) Φhat s
  let a : ℂ → BilateralLaurentSeries := fun u =>
    equalRankSliceCoefficient T μ ψ f.val
      (translateInverseWhittaker ψ (U u) ((-1) ^ t)) Φ
  let ad : ℂ → BilateralLaurentSeries := fun u =>
    equalRankSliceCoefficient T μ (ψ.scale (-1))
      (firstDualFunction ψ t f.val) (secondDualFunction ψ t (U u)) Φhat
  have hdata : ∀ u : ℂ, ∃ R Rd : RationalFunctions,
      HasRationalContinuation qF (I u) R ∧
      HasRationalContinuation qF (Id u) Rd ∧
      HasAbsoluteBilateralSpectralExpansion qF (a u) (I u) ∧
      HasAbsoluteBilateralSpectralExpansion qF (ad u) (Id u) := by
    intro u
    obtain ⟨ellU, hellU, v, hv⟩ := hcoeff u
    let τ := complexOppositeTwistInduced F m h σ u
    have hτ := complexOppositeTwistInduced_inverseWhittakerType F h ψ σ hσ u
    let fU := modelMap τ ellU v
    have hfU : fU.val = U u := hv
    let fUc := modelMap τ ellU (τ ((-1) ^ t) v)
    have hfUc : fUc.val = translateInverseWhittaker ψ (U u) ((-1) ^ t) := by
      rw [← hfU]
      exact (translateInverseWhittaker_coefficient ψ τ ellU v ((-1) ^ t)).symm
    obtain ⟨R, hR, ha⟩ := equalRankCoefficient_continuationData F ψ μ hμ
      π τ hπ hτ lambda ellU hlambda hellU f fUc Φ
    obtain ⟨Rd, hRd, had⟩ := equalRankCoefficient_continuationData F (ψ.scale (-1)) μ hμ
      (inverseTransposePullback π) (inverseTransposePullback τ)
      (isOfWhittakerType_firstDual ψ π hπ) (isOfWhittakerType_secondDual ψ τ hτ)
      (firstDualFunctional ψ π lambda) (secondDualFunctional ψ τ ellU)
      (firstDualFunctional_ne_zero ψ π hlambda) (secondDualFunctional_ne_zero ψ τ hellU)
      (firstDualModelMap ψ π lambda f) (secondDualModelMap ψ τ ellU fU) Φhat
    change HasRationalContinuation qF (fun s => equalRankIntegral _ abv μ
      (firstDualFunction ψ t f.val) (secondDualFunction ψ t fU.val) Φhat s) Rd at hRd
    change HasAbsoluteBilateralSpectralExpansion qF
      (equalRankSliceCoefficient T μ (ψ.scale (-1))
        (firstDualFunction ψ t f.val) (secondDualFunction ψ t fU.val) Φhat)
      (fun s => equalRankIntegral _ abv μ
        (firstDualFunction ψ t f.val) (secondDualFunction ψ t fU.val) Φhat s) at had
    rw [hfUc] at hR ha
    rw [hfU] at hRd had
    exact ⟨R, Rd, hR, hRd, ha, had⟩
  choose R Rd hR hRd ha had using hdata
  have hFE : ∀ u : ℝ, Cbound < u →
      GammaFunctionalEquation qF 1 t
        (oppositeSpectralGammaProduct qF F.canonicalTopologicalData.residueCardinality_gt_one G₀ G₁ (u : ℂ))
        (R (u : ℂ)) (Rd (u : ℂ)) := by
    intro u hu
    obtain ⟨ellU, hellU, v, hv⟩ := hcoeff (u : ℂ)
    let τ := complexOppositeTwistInduced F m h σ (u : ℂ)
    let fU := modelMap τ ellU v
    have hfU : fU.val = U (u : ℂ) := hv
    have hg := isPairGammaFactor_self.mp
      ((isPadicSymmetricGammaFactor_of_le (le_refl t)).mp (hgamma u hu))
    obtain ⟨ζu, hζu, -, hall⟩ := hg.2.2.2 μ hμ lambda ellU hlambda hellU
    obtain ⟨Φu, S, Sd, hΦu, hS, hSd, hN⟩ := hall f fU Φ
    have heΦ : Φu = Φhat := hΦu.unique hΦ
    rw [heΦ] at hSd
    have hSc := RationalContinuationLinear.continuation_of_eq_on_right
      (hasRationalContinuation_const_mul ((ζu : ℂ) ^ t) hS)
      ⟨0, fun s _ => equalRankIntegral_central_translate ψ τ ellU μ abv hζu f.val fU Φ s⟩
    change HasRationalContinuation qF (fun s => equalRankIntegral (ψ.scale (-1))
      abv μ (firstDualFunction ψ t f.val) (secondDualFunction ψ t fU.val) Φhat s) Sd at hSd
    rw [hfU] at hSc hSd
    have he : RatFunc.C ((ζu : ℂ) ^ t) * S = R (u : ℂ) :=
      hSc.unique F.canonicalTopologicalData.residueCardinality_gt_one (hR _)
    have hed : Sd = Rd (u : ℂ) := hSd.unique F.canonicalTopologicalData.residueCardinality_gt_one (hRd _)
    have hN' := (gammaFunctionalEquation_absorb_scalar F.canonicalTopologicalData.residueCardinality_gt_one
      (LocalFactor.coe_residueReflection F)).mp hN
    simpa only [he, hed] using hN'
  have hclears : ∀ u : ℝ, Cbound < u → ∃ L : LaurentPolynomial ℂ,
      oppositeSpectralClearingKernel qF P₀ P₁ (u : ℂ) • a (u : ℂ) =
        BilateralLaurentSeries.ofLaurentPolynomial L := by
    intro u hu
    obtain ⟨ellU, hellU, v, hv⟩ := hcoeff (u : ℂ)
    let τ := complexOppositeTwistInduced F m h σ (u : ℂ)
    obtain ⟨L, hL⟩ := hclear u hu ellU hellU f
      (modelMap τ ellU (τ ((-1) ^ t) v)) Φ
    have hfUc : (modelMap τ ellU (τ ((-1) ^ t) v)).val =
        translateInverseWhittaker ψ (U (u : ℂ)) ((-1) ^ t) :=
      (translateInverseWhittaker_coefficient ψ τ ellU v ((-1) ^ t)).symm.trans
        (congrArg (fun z => translateInverseWhittaker ψ z ((-1) ^ t)) hv)
    rw [hfUc] at hL
    exact ⟨L, hL.symm⟩
  have hN := gammaFE_oppositeSpectralProduct_at_zero F.canonicalTopologicalData.residueCardinality_gt_one
    G₀ G₁ P₀ P₁ hP hae hade hR hRd ha had Cbound hclears hFE
  obtain ⟨S, hS, -⟩ := equalRankCoefficient_continuationData F ψ μ hμ π
    (TwoBlockJacquet.inducedRep F h σ) hπ
    (lowerInduced_inverseWhittakerType F h ψ σ hσ)
    lambda ell hlambda hell f f' Φ
  have hSc := RationalContinuationLinear.continuation_of_eq_on_right
    (hasRationalContinuation_const_mul ((ζ : ℂ) ^ t) hS)
    ⟨0, fun s _ => equalRankIntegral_central_translate ψ
      (TwoBlockJacquet.inducedRep F h σ) ell μ abv hζ f.val f' Φ s⟩
  have hSc0 : HasRationalContinuation qF (I 0) (RatFunc.C ((ζ : ℂ) ^ t) * S) := by
    simpa only [I, hU0] using hSc
  have he0 := hSc0.unique F.canonicalTopologicalData.residueCardinality_gt_one (hR 0)
  refine ⟨S, Rd 0, hS, ?_, ?_⟩
  · simpa only [Id, hU0, dualEqualRankModelIntegral] using hRd 0
  · apply (gammaFunctionalEquation_absorb_scalar F.canonicalTopologicalData.residueCardinality_gt_one
      (LocalFactor.coe_residueReflection F)).mpr
    simpa only [he0] using hN

end ActualContinuation

/-- The actual opposite-twist equations identify the complete gamma factor
of the original equal-rank lower induction with the two original block factors. -/
theorem equalTwoBlockSymmetricGammaProduct_at_zero
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) :
    EqualTwoBlockSymmetricGammaProduct F h ψ ν π σ := by
  let := unipotentHaar_isMulRightInvariant F.Carrier t
  let μ := unipotentQuotientHaar F.Carrier t
  have hμ := unipotentQuotientHaar_isCompatible F.Carrier t
  have hq := F.canonicalTopologicalData.residueCardinality_gt_one
  have hIndInv := lowerInduced_inverseWhittakerType F h ψ σ hσ
  have hInd := (isOfWhittakerType_standard_iff_inverse ψ _).mpr hIndInv
  obtain ⟨lambda, hlambda⟩ := hπ.exists_ne_zero
  obtain ⟨ell, hell⟩ := hIndInv.exists_ne_zero
  let g₀ := padicSymmetricGammaFactorOfWhittakerType F ψ ν.val π (σ 0)
    (whittakerTypeGammaConstructionInput p F ψ ν t (m 0) V (W 0)
      π (σ 0) hπ (hσ 0))
  let g₁ := padicSymmetricGammaFactorOfWhittakerType F ψ ν.val π (σ 1)
    (whittakerTypeGammaConstructionInput p F ψ ν t (m 1) V (W 1)
      π (σ 1) hπ (hσ 1))
  obtain ⟨P₀, hP₀⟩ := symmetricLPolynomialExists p F ψ ν t (m 0) V
    (W 0) π (σ 0) hπ (hσ 0)
  obtain ⟨P₁, hP₁⟩ := symmetricLPolynomialExists p F ψ ν t (m 1) V
    (W 1) π (σ 1) hπ (hσ 1)
  have hP : P₀ * P₁ ≠ 0 := by
    have hc : (P₀ * P₁).coeff 0 = 1 := by
      rw [Polynomial.mul_coeff_zero, hP₀.coeff_zero, hP₁.coeff_zero, one_mul]
    intro hz
    simp [hz] at hc
  obtain ⟨CL, hclear⟩ := exists_equalOppositeRealRayClearing F h ψ ν π σ
    hπ hσ μ hμ lambda hlambda P₀ P₁ hP₀ hP₁
  obtain ⟨CG, hgamma⟩ := exists_equalOppositeRealRayGammaCertificates F h ψ ν π σ
    hπ hσ g₀.val g₁.val g₀.property g₁.property
  have hclear' : EqualOppositeRealRayClearing F h ψ π σ μ lambda P₀ P₁ (max CL CG) :=
    fun u hu => hclear u (lt_of_le_of_lt (le_max_left CL CG) hu)
  have hgamma' : EqualOppositeRealRayGammaCertificates F h ψ ν π σ g₀.val g₁.val
      (max CL CG) :=
    fun u hu => hgamma u (lt_of_le_of_lt (le_max_right CL CG) hu)
  let g := padicSymmetricGammaFactorOfWhittakerType F ψ ν.val π
    (TwoBlockJacquet.inducedRep F h σ)
    (whittakerTypeGammaConstructionInput p F ψ ν t t V
      (TwoBlockJacquet.Sections F h σ) π (TwoBlockJacquet.inducedRep F h σ) hπ hInd)
  have hEq := (isPairGammaFactor_self.mp
    ((isPadicSymmetricGammaFactor_of_le (le_refl t)).mp g.property)).2.2.2
      μ hμ lambda ell hlambda hell
  obtain ⟨ζ, hζ, ⟨R₀, ⟨f, f', Φ, hR₀⟩, hR₀0⟩, hFE⟩ := hEq
  obtain ⟨Φhat, R, Rd, hΦ, hR, hRd, hN⟩ := hFE f f' Φ
  obtain ⟨S, Sd, hS, hSd, hM⟩ := equalTwoBlock_gamma_at_zero F h ψ ν π σ μ hμ
    hπ hσ lambda hlambda ell hell f f' Φ Φhat hΦ ζ hζ g₀.val g₁.val P₀ P₁ hP
    (max CL CG) hclear' hgamma'
  have he : R = S := hR.unique hq hS
  have hed : Rd = Sd := hRd.unique hq hSd
  have hS0 : S ≠ 0 := by rwa [← hR₀.unique hq hS]
  rw [he, hed] at hN
  have hg : (g.val : RationalFunctions) =
      (g₀.val : RationalFunctions) * (g₁.val : RationalFunctions) :=
    hN.gamma_unique hq hS0 hM
  exact ⟨g₀.val, g₁.val, g₀.property, g₁.property, by rw [← hg]; exact g.property⟩

end Langlands.RankinSelberg.DominantRankTransport
