import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictLContinuation
import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictGammaBound
import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualGammaContinuation

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  ParameterSpecialization AdjacentGammaContinuation LocalFactor Polynomial AdjacentBlockReduction

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance strictGammaContinuationTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance strictGammaContinuationValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance strictGammaContinuationLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance strictGammaContinuationT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance strictGammaContinuationSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance strictGammaContinuationSigmaCompact : SigmaCompactSpace F.Carrier :=
  F.canonicalTopologicalData.sigmaCompactSpace
local instance strictGammaContinuationMeasurable : MeasurableSpace F.Carrier := borel _
local instance strictGammaContinuationBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance strictGammaContinuationGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance strictGammaContinuationGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictGammaContinuationUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance strictGammaContinuationUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictGammaContinuationQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance strictGammaContinuationQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue T

section CentralTranslation

/-- The fixed central translation absorbs the model sign with the exponent
of the larger rank in the actual strict integral. -/
theorem strictIntegral_central_translate {n r j k : ℕ}
    (hr : r = n + (j + k + 1)) (ψ : UnitaryAdditiveCharacter F.Carrier)
    {Z : Type uW} [AddCommGroup Z] [Module ℂ Z]
    (τ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) Z)
    (ell : glInverseFunctionals ψ n τ)
    (μ : Measure (LeftUnipotentQuotient n F.Carrier))
    (ν : AdditiveHaarMeasure F.Carrier)
    {ζ : ℂˣ} (hζ : HasModelMinusOneScalar τ ell ζ)
    (f : WhittakerFunctions ψ r) (f' : (coefficientModel τ ell).toSubmodule) (s : ℂ) :
    unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν j (n + 1)) f
        (translateInverseWhittaker ψ f'.val ((-1) ^ r)) s =
      (ζ : ℂ) ^ r * unequalRankIntegralAt j k hr ψ abv μ
        (rectangularMeasure ν j (n + 1)) f f'.val s := by
  have hf (g : GeneralLinear (n + 1) F.Carrier) :
      (translateInverseWhittaker ψ f'.val ((-1) ^ r)).val g =
        (ζ : ℂ) ^ r * f'.val.val g := by
    have hc : Commute (-1 : GeneralLinear (n + 1) F.Carrier) g := by
      apply Units.ext
      simp
    change f'.val.val (g * (-1) ^ r) = _
    rw [← (hc.pow_left r).eq, hζ.pow_apply]
  rw [unequalRankIntegralAt_eq_outer, unequalRankIntegralAt_eq_outer]
  simp_rw [hf]
  calc
    _ = ∫ q, (ζ : ℂ) ^ r *
        ((∫ X, f.val (blockMatrixAt j k hr q.out X) ∂rectangularMeasure ν j (n + 1)) *
          f'.val.val q.out * determinantWeight abv q.out (s - ((j + k + 1 : ℕ) : ℂ) / 2)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with q
      ring
    _ = _ := integral_const_mul _ _

end CentralTranslation

variable {t r : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (htr : t < r)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))

/-- Complete certificates for the fixed opposite spectral gamma product. -/
def StrictOppositeRealRayGammaCertificates
    (G₀ G₁ : RationalFunctions) (Cbound : ℝ) : Prop :=
  ∀ u : ℝ, Cbound < u →
    IsPadicSymmetricGammaFactor F ψ ν.val π
      (complexOppositeTwistInduced F m h σ (u : ℂ))
      (oppositeSpectralGammaProduct qF F.canonicalTopologicalData.residueCardinality_gt_one G₀ G₁ (u : ℂ))

include htr in
/-- Unramified transport and complete-certificate uniqueness identify the
large-real-twist witnesses with the two fixed original block factors. -/
theorem exists_strictOppositeRealRayGammaCertificates
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (G₀ G₁ : RationalFunctions)
    (hG₀ : IsPadicSymmetricGammaFactor F ψ ν.val π (σ 0) G₀)
    (hG₁ : IsPadicSymmetricGammaFactor F ψ ν.val π (σ 1) G₁) :
    ∃ Cbound : ℝ, StrictOppositeRealRayGammaCertificates F h ψ ν π σ G₀ G₁ Cbound := by
  obtain ⟨Cbound, hC⟩ := exists_strictTwoBlockSymmetricGammaProduct F h htr ψ ν π σ
    twoBlockDominantFirstBlockLaurentIdentity hπ hσ
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

variable (j k : ℕ) (hr : r = t + (j + k + 1))
  [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
  (μ : Measure (LeftUnipotentQuotient t F.Carrier)) [IsFiniteMeasureOnCompacts μ]
  (hμ : IsCompatible (upperUnipotent (t + 1) F.Carrier)
    (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μ)
  (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
  (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
  (lambda : glFunctionals ψ r π) (hlambda : lambda.val ≠ 0)
  (ell : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
  (hell : ell.val ≠ 0)
  (f : (coefficientModel π lambda).toSubmodule)
  (f' : (coefficientModel (TwoBlockJacquet.inducedRep F h σ) ell).toSubmodule)
  (ζ : ℂˣ) (hζ : HasModelMinusOneScalar (TwoBlockJacquet.inducedRep F h σ) ell ζ)
  (G₀ G₁ : RationalFunctions) (P₀ P₁ : Polynomial ℂ) (hP : P₀ * P₁ ≠ 0)
  (Cbound : ℝ)
  (hclear : StrictOppositeRealRayClearing F h ψ ν π σ μ lambda P₀ P₁ Cbound)
  (hgamma : StrictOppositeRealRayGammaCertificates F h ψ ν π σ G₀ G₁ Cbound)

include htr hμ hπ hσ hlambda hell hζ hP hclear hgamma

set_option maxHeartbeats 1800000 in
/-- Continue the sign-absorbed strict gamma equations with the actual fixed
right-Weyl first dual and swapped rectangular rows, then restore the sign. -/
theorem strictTwoBlock_gamma_at_zero :
    ∃ R Rd : RationalFunctions,
      HasRationalContinuation qF
        (unequalRankIntegralAt j k hr ψ abv μ (rectangularMeasure ν.val j (t + 1))
          f.val f'.val) R ∧
      HasRationalContinuation qF
        (dualUnequalRankModelIntegralAt htr j k hr ψ abv μ ν.val π
          (TwoBlockJacquet.inducedRep F h σ) lambda ell f f') Rd ∧
      GammaFunctionalEquation qF ζ r (G₀ * G₁) R Rd := by
  classical
  obtain ⟨U, hU0, hcoeff, ⟨K, hKo, hKc, hK⟩, hUa⟩ :=
    exists_oppositeWhittakerFamily F m h σ ψ hσ ell hell f'
  have hrd : r = t + (k + j + 1) := by omega
  let fd := translatedFirstDualModelEquiv ψ π lambda (blockWeylAt t r htr) f
  obtain ⟨⟨L, hLo, -, hL⟩, hUca⟩ :=
    inverseWhittaker_translate_level_entire F ψ U K hKo hKc hK hUa ((-1) ^ r)
  obtain ⟨⟨Ld, hLdo, -, hLd⟩, hUda⟩ :=
    inverseWhittaker_secondDual_level_entire F ψ U K hKo hKc hK hUa
  have hae := strictSlices_entire F hr ψ μ ν.val π hπ lambda hlambda f
    (fun u => translateInverseWhittaker ψ (U u) ((-1) ^ r)) L hLo hL hUca
  have hade := strictSlices_entire F hrd (ψ.scale (-1)) μ ν.val
    (inverseTransposePullback π) (isOfWhittakerType_firstDual ψ π hπ)
    (firstDualFunctional ψ π lambda) (firstDualFunctional_ne_zero ψ π hlambda) fd
    (fun u => secondDualFunction ψ t (U u)) Ld hLdo hLd hUda
  let I := fun u => unequalRankIntegralAt j k hr ψ abv μ
    (rectangularMeasure ν.val j (t + 1)) f.val
    (translateInverseWhittaker ψ (U u) ((-1) ^ r))
  let Id := fun u => unequalRankIntegralAt k j hrd (ψ.scale (-1)) abv μ
    (rectangularMeasure ν.val k (t + 1)) fd.val (secondDualFunction ψ t (U u))
  let a : ℂ → HarmonicAnalysis.BilateralLaurentSeries := fun u =>
    strictSliceCoefficient F hr ψ μ ν.val f.val
      (translateInverseWhittaker ψ (U u) ((-1) ^ r))
  let ad : ℂ → HarmonicAnalysis.BilateralLaurentSeries := fun u =>
    strictSliceCoefficient F hrd (ψ.scale (-1)) μ ν.val fd.val
      (secondDualFunction ψ t (U u))
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
    let fUc := modelMap τ ellU (τ ((-1) ^ r) v)
    have hfUc : fUc.val = translateInverseWhittaker ψ (U u) ((-1) ^ r) := by
      rw [← hfU]
      exact (translateInverseWhittaker_coefficient ψ τ ellU v ((-1) ^ r)).symm
    obtain ⟨R, hR, ha⟩ := strictRankCoefficient_continuationData F hr ψ μ ν.val hμ
      π τ hπ hτ lambda ellU hlambda hellU f fUc
    obtain ⟨Rd, hRd, had⟩ := strictRankCoefficient_continuationData F hrd (ψ.scale (-1)) μ ν.val hμ
      (inverseTransposePullback π) (inverseTransposePullback τ)
      (isOfWhittakerType_firstDual ψ π hπ) (isOfWhittakerType_secondDual ψ τ hτ)
      (firstDualFunctional ψ π lambda) (secondDualFunctional ψ τ ellU)
      (firstDualFunctional_ne_zero ψ π hlambda) (secondDualFunctional_ne_zero ψ τ hellU)
      fd (secondDualModelMap ψ τ ellU fU)
    change HasRationalContinuation qF (unequalRankIntegralAt k j hrd (ψ.scale (-1)) abv μ
      (rectangularMeasure ν.val k (t + 1)) fd.val (secondDualFunction ψ t fU.val)) Rd at hRd
    change HasAbsoluteBilateralSpectralExpansion qF
      (strictSliceCoefficient F hrd (ψ.scale (-1)) μ ν.val fd.val
        (secondDualFunction ψ t fU.val))
      (unequalRankIntegralAt k j hrd (ψ.scale (-1)) abv μ
        (rectangularMeasure ν.val k (t + 1)) fd.val (secondDualFunction ψ t fU.val)) at had
    rw [hfUc] at hR ha
    rw [hfU] at hRd had
    exact ⟨R, Rd, hR, hRd, ha, had⟩
  choose R Rd hR hRd ha had using hdata
  have hFE : ∀ u : ℝ, Cbound < u →
      GammaFunctionalEquation qF 1 r
        (oppositeSpectralGammaProduct qF F.canonicalTopologicalData.residueCardinality_gt_one G₀ G₁ (u : ℂ))
        (R (u : ℂ)) (Rd (u : ℂ)) := by
    intro u hu
    obtain ⟨ellU, hellU, v, hv⟩ := hcoeff (u : ℂ)
    let τ := complexOppositeTwistInduced F m h σ (u : ℂ)
    let fU := modelMap τ ellU v
    have hfU : fU.val = U (u : ℂ) := hv
    have hg := (isPairGammaFactor_of_lt htr).mp
      ((isPadicSymmetricGammaFactor_of_le htr.le).mp (hgamma u hu))
    obtain ⟨ζu, hζu, hall⟩ := hg.2.2.2 μ hμ lambda ellU hlambda hellU
    obtain ⟨S, Sd, hS, hSd, hN⟩ := (hall j k hr).2 f fU
    have hSc := RationalContinuationLinear.continuation_of_eq_on_right
      (hasRationalContinuation_const_mul ((ζu : ℂ) ^ r) hS)
      ⟨0, fun s _ => strictIntegral_central_translate F hr ψ τ ellU μ ν.val hζu f.val fU s⟩
    change HasRationalContinuation qF
      (unequalRankIntegralAt k j hrd (ψ.scale (-1)) abv μ
        (rectangularMeasure ν.val k (t + 1)) fd.val (secondDualFunction ψ t fU.val)) Sd at hSd
    rw [hfU] at hSc hSd
    have he : RatFunc.C ((ζu : ℂ) ^ r) * S = R (u : ℂ) :=
      hSc.unique F.canonicalTopologicalData.residueCardinality_gt_one (hR _)
    have hed : Sd = Rd (u : ℂ) := hSd.unique F.canonicalTopologicalData.residueCardinality_gt_one (hRd _)
    have hN' := (gammaFunctionalEquation_absorb_scalar F.canonicalTopologicalData.residueCardinality_gt_one
      (LocalFactor.coe_residueReflection F)).mp hN
    simpa only [he, hed] using hN'
  have hclears : ∀ u : ℝ, Cbound < u → ∃ L : LaurentPolynomial ℂ,
      oppositeSpectralClearingKernel qF P₀ P₁ (u : ℂ) • a (u : ℂ) =
        HarmonicAnalysis.BilateralLaurentSeries.ofLaurentPolynomial L := by
    intro u hu
    obtain ⟨ellU, hellU, v, hv⟩ := hcoeff (u : ℂ)
    let τ := complexOppositeTwistInduced F m h σ (u : ℂ)
    obtain ⟨L, hL⟩ := hclear u hu ellU hellU j k hr f
      (modelMap τ ellU (τ ((-1) ^ r) v))
    have hfUc : (modelMap τ ellU (τ ((-1) ^ r) v)).val =
        translateInverseWhittaker ψ (U (u : ℂ)) ((-1) ^ r) :=
      (translateInverseWhittaker_coefficient ψ τ ellU v ((-1) ^ r)).symm.trans
        (congrArg (fun z => translateInverseWhittaker ψ z ((-1) ^ r)) hv)
    rw [hfUc] at hL
    exact ⟨L, hL.symm⟩
  have hN := gammaFE_oppositeSpectralProduct_at_zero F.canonicalTopologicalData.residueCardinality_gt_one
    G₀ G₁ P₀ P₁ hP hae hade hR hRd ha had Cbound hclears hFE
  obtain ⟨S, hS, -⟩ := strictRankCoefficient_continuationData F hr ψ μ ν.val hμ π
    (TwoBlockJacquet.inducedRep F h σ) hπ
    (lowerInduced_inverseWhittakerType F h ψ σ hσ)
    lambda ell hlambda hell f f'
  have hSc := RationalContinuationLinear.continuation_of_eq_on_right
    (hasRationalContinuation_const_mul ((ζ : ℂ) ^ r) hS)
    ⟨0, fun s _ => strictIntegral_central_translate F hr ψ
      (TwoBlockJacquet.inducedRep F h σ) ell μ ν.val hζ f.val f' s⟩
  have hSc0 : HasRationalContinuation qF (I 0) (RatFunc.C ((ζ : ℂ) ^ r) * S) := by
    simpa only [I, hU0] using hSc
  have he0 := hSc0.unique F.canonicalTopologicalData.residueCardinality_gt_one (hR 0)
  refine ⟨S, Rd 0, hS, ?_, ?_⟩
  · simpa only [Id, hU0, dualUnequalRankModelIntegralAt, fd,
      translatedFirstDualModelEquiv_val] using hRd 0
  · apply (gammaFunctionalEquation_absorb_scalar F.canonicalTopologicalData.residueCardinality_gt_one
      (LocalFactor.coe_residueReflection F)).mpr
    simpa only [he0] using hN

end ActualContinuation

include htr in
/-- The actual opposite-twist equations identify the complete gamma factor
of the original strict-rank lower induction with the two original block factors. -/
theorem strictTwoBlockSymmetricGammaProduct_at_zero
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) :
    StrictTwoBlockSymmetricGammaProduct F h ψ ν π σ := by
  let := unipotentHaar_isMulRightInvariant F.Carrier t
  let μ := unipotentQuotientHaar F.Carrier t
  have hμ := unipotentQuotientHaar_isCompatible F.Carrier t
  have hq := F.canonicalTopologicalData.residueCardinality_gt_one
  have hIndInv := lowerInduced_inverseWhittakerType F h ψ σ hσ
  have hInd := (isOfWhittakerType_standard_iff_inverse ψ _).mpr hIndInv
  obtain ⟨lambda, hlambda⟩ := hπ.exists_ne_zero
  obtain ⟨ell, hell⟩ := hIndInv.exists_ne_zero
  let g₀ := padicSymmetricGammaFactorOfWhittakerType F ψ ν.val π (σ 0)
    (whittakerTypeGammaConstructionInput p F ψ ν r (m 0) V (W 0)
      π (σ 0) hπ (hσ 0))
  let g₁ := padicSymmetricGammaFactorOfWhittakerType F ψ ν.val π (σ 1)
    (whittakerTypeGammaConstructionInput p F ψ ν r (m 1) V (W 1)
      π (σ 1) hπ (hσ 1))
  obtain ⟨P₀, hP₀⟩ := symmetricLPolynomialExists p F ψ ν r (m 0) V
    (W 0) π (σ 0) hπ (hσ 0)
  obtain ⟨P₁, hP₁⟩ := symmetricLPolynomialExists p F ψ ν r (m 1) V
    (W 1) π (σ 1) hπ (hσ 1)
  have hP : P₀ * P₁ ≠ 0 := by
    have hc : (P₀ * P₁).coeff 0 = 1 := by
      rw [Polynomial.mul_coeff_zero, hP₀.coeff_zero, hP₁.coeff_zero, one_mul]
    intro hz
    simp [hz] at hc
  obtain ⟨CL, hclear⟩ := exists_strictOppositeRealRayClearing F h htr ψ ν π σ
    hπ hσ μ hμ lambda hlambda P₀ P₁ hP₀ hP₁
  obtain ⟨CG, hgamma⟩ := exists_strictOppositeRealRayGammaCertificates F h htr ψ ν π σ
    hπ hσ g₀.val g₁.val g₀.property g₁.property
  have hclear' : StrictOppositeRealRayClearing F h ψ ν π σ μ lambda P₀ P₁ (max CL CG) :=
    fun u hu => hclear u (lt_of_le_of_lt (le_max_left CL CG) hu)
  have hgamma' : StrictOppositeRealRayGammaCertificates F h ψ ν π σ g₀.val g₁.val
      (max CL CG) :=
    fun u hu => hgamma u (lt_of_le_of_lt (le_max_right CL CG) hu)
  let g := padicSymmetricGammaFactorOfWhittakerType F ψ ν.val π
    (TwoBlockJacquet.inducedRep F h σ)
    (whittakerTypeGammaConstructionInput p F ψ ν r t V
      (TwoBlockJacquet.Sections F h σ) π (TwoBlockJacquet.inducedRep F h σ) hπ hInd)
  have hEq := ((isPairGammaFactor_of_lt htr).mp
    ((isPadicSymmetricGammaFactor_of_le htr.le).mp g.property)).2.2.2
      μ hμ lambda ell hlambda hell
  obtain ⟨ζ, hζ, hall⟩ := hEq
  have hr0 : r = t + (0 + (r - t - 1) + 1) := by omega
  obtain ⟨⟨R₀, hR₀mem, hR₀0⟩, hFE⟩ := hall 0 (r - t - 1) hr0
  rw [unequalRankValuesAt_eq_set] at hR₀mem
  obtain ⟨f, f', hR₀⟩ := hR₀mem
  obtain ⟨R, Rd, hR, hRd, hN⟩ := hFE f f'
  obtain ⟨S, Sd, hS, hSd, hM⟩ := strictTwoBlock_gamma_at_zero F h htr ψ ν π σ 0 (r - t - 1) hr0 μ hμ
    hπ hσ lambda hlambda ell hell f f' ζ hζ g₀.val g₁.val P₀ P₁ hP
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
