import Langlands.Representation.RankinSelberg.AdjacentRankSpectralGammaContinuation
import Langlands.Representation.RankinSelberg.AdjacentRankDualEntireCoefficientFamily
import Langlands.Representation.RankinSelberg.AdjacentRankCertifiedRealRay
import Langlands.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationProof

/-! Actual corank integrals in second-block gamma continuation. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open ParameterSpecialization AdjacentGammaContinuation
open scoped BigOperators

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance corankGammaTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance corankGammaValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance corankGammaLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance corankGammaFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance corankGammaFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance corankGammaGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance corankGammaGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance corankGammaUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (upperUnipotent (r + 1) F.Carrier) := borel _
local instance corankGammaUnipotentBorel (r : ℕ) :
    BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance corankGammaQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F.Carrier) := borel _
local instance corankGammaQuotientBorel (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "T" => F.canonicalTopologicalData
local notation "abv" => normalizedAbsoluteValue T
local notation "qF" => F.canonicalTopologicalData.residueCardinality

/-- Full type gives a rational continuation and an actual absolute spectral
expansion of the same corank coefficient vector. -/
theorem corankOneCoefficient_continuationData
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    (μ : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1 + 1) F.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓU : glFunctionals ψ (r + 1) π) (hℓU : ℓU.val ≠ 0)
    (ℓprime : glInverseFunctionals ψ r τ) (hℓprime : ℓprime.val ≠ 0)
    (U : (coefficientModel π ℓU).toSubmodule)
    (Wprime : (coefficientModel τ ℓprime).toSubmodule) :
    ∃ R : RationalFunctions,
      HasRationalContinuation qF (fun s =>
        corankOneIntegral ψ abv ν U.val Wprime.val s) R ∧
      HasAbsoluteBilateralSpectralExpansion qF
        (corankCoefficientSeries F ψ ν U.val Wprime.val)
        (fun s => corankOneIntegral ψ abv ν U.val Wprime.val s) := by
  have han := unequalRankAnalytic F T r 0 0 ψ ν hν μ
    V W π τ hπ hτ ℓU ℓprime hℓU hℓprime
  obtain ⟨R, hR⟩ := han.2.1 U Wprime
  have hRc := RationalContinuationLinear.continuation_of_eq_on_right hR
    ⟨0, fun s _ => corankOneIntegral_eq_zeroZero F ψ ν μ U.val Wprime.val s⟩
  obtain ⟨C, hC⟩ := corankOneCoefficient_convergesOnRight F ψ ν hν μ
    π τ hπ hτ ℓU ℓprime hℓU hℓprime U Wprime
  exact ⟨R, hRc, C, fun s hs =>
    corankOneSliceExpansion F ψ U.val Wprime.val ν s (hC s hs)⟩

/-- Complete real-ray certificates for the actual second-block deformation
with the fixed spectral product. -/
def SecondBlockCorankRealRayGammaCertificates
    {r : ℕ} (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : AdditiveHaarMeasure F.Carrier)
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = (r + 1) + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (G₀ G₁ : RationalFunctions) (C : ℝ) : Prop :=
  ∀ u : ℝ, C < u →
    IsPadicSymmetricGammaFactor F ψ μ
      (twoBlockSecondDeformedInduced F m h σ (u : ℂ)) τ
      (spectralGammaProduct qF F.canonicalTopologicalData.residueCardinality_gt_one G₀ G₁ (u : ℂ))

/-- Continue the real-ray gamma products to every specified original model
vector, using its actual original and translated dual corank integrals. -/
theorem secondBlock_corankGamma_at_zero
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = (r + 1) + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (ℓ₀ : glFunctionals ψ (r + 1) (twoBlockSecondDeformedInduced F m h σ 0))
    (hℓ₀ : ℓ₀.val ≠ 0)
    (W₀ : (coefficientModel (twoBlockSecondDeformedInduced F m h σ 0) ℓ₀).toSubmodule)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    (μ : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓprime : glInverseFunctionals ψ r τ) (hℓprime : ℓprime.val ≠ 0)
    (Wprime : (coefficientModel τ ℓprime).toSubmodule)
    (ζ : ℂˣ) (hζ : HasModelMinusOneScalar τ ℓprime ζ)
    (G₀ G₁ : RationalFunctions)
    (P₀ P₁ : Polynomial ℂ) (hP : P₀ * P₁ ≠ 0) (C : ℝ)
    (hclear : SecondBlockCorankRealRayClearing F ψ m h σ ν Wprime.val P₀ P₁ C)
    (hgamma : SecondBlockCorankRealRayGammaCertificates F ψ μ m h σ τ G₀ G₁ C) :
    ∃ R Rd : RationalFunctions,
      HasRationalContinuation qF (fun s =>
        corankOneIntegral ψ abv ν W₀.val Wprime.val s) R ∧
      HasRationalContinuation qF
        (dualUnequalRankModelIntegralAt (Nat.lt_succ_self r) 0 0 rfl ψ abv ν μ
          (twoBlockSecondDeformedInduced F m h σ 0) τ ℓ₀ ℓprime W₀ Wprime) Rd ∧
      GammaFunctionalEquation qF ζ (r + 1) (G₀ * G₁) R Rd := by
  classical
  obtain ⟨U, hzero, hcoeff, hK, hU, -, hae⟩ :=
    secondBlock_entireCorankFamily F twoBlockSecondWhittakerDeformation ψ r
      m h σ hσ ℓ₀ hℓ₀ W₀ ν hν τ hτ ℓprime Wprime
  have hade := (adjacentRankDualCoefficientFamily_integrable_entire F ψ r ν hν
    τ hτ ℓprime Wprime U hK hU).2
  let I := fun u s => corankOneIntegral ψ abv ν (U u) Wprime.val s
  let Id := fun u s => corankOneIntegral (ψ.scale (-1)) abv ν
    (adjacentRankDualWhittakerFamily F ψ r U u) (secondDualFunction ψ r Wprime.val) s
  have hdata : ∀ u : ℂ, ∃ R Rd : RationalFunctions,
      HasRationalContinuation qF (I u) R ∧
      HasRationalContinuation qF (Id u) Rd ∧
      HasAbsoluteBilateralSpectralExpansion qF
        (corankCoefficientFamily F ψ ν Wprime.val U u) (I u) ∧
      HasAbsoluteBilateralSpectralExpansion qF
        (adjacentRankDualCoefficientFamily F ψ ν Wprime.val U u) (Id u) := by
    intro u
    obtain ⟨ℓu, hℓu, v, hv⟩ := hcoeff u
    let π := twoBlockSecondDeformedInduced F m h σ u
    have hπ := secondBlockDeformed_isOfWhittakerType F ψ m h σ hσ u
    let f := modelMap π ℓu v
    have hf : f.val = U u := hv
    obtain ⟨R, hR, ha⟩ := corankOneCoefficient_continuationData F ψ ν hν μ
      π τ hπ hτ ℓu hℓu ℓprime hℓprime f Wprime
    have hπd : IsOfWhittakerType (r + 1)
        (standardCharacter (ψ.scale (-1)) (r + 1)) (inverseTransposePullback π) := by
      simpa only [standardCharacter_scale_neg_one] using
        isOfWhittakerType_inverseTransposePullback ψ π hπ
    have hτd : IsOfWhittakerType r (inverseStandardCharacter (ψ.scale (-1)) r)
        (inverseTransposePullback τ) := by
      simpa only [inverseStandardCharacter_scale_neg_one] using
        isOfWhittakerType_inverseTransposePullback_inverse ψ τ hτ
    let fd := translatedFirstDualModelEquiv ψ π ℓu
      (blockWeylAt r (r + 1) (Nat.lt_succ_self r)) f
    obtain ⟨Rd, hRd, had⟩ := corankOneCoefficient_continuationData F (ψ.scale (-1))
      ν hν μ (inverseTransposePullback π) (inverseTransposePullback τ) hπd hτd
      (firstDualFunctional ψ π ℓu) (firstDualFunctional_ne_zero ψ π hℓu)
      (secondDualFunctional ψ τ ℓprime) (secondDualFunctional_ne_zero ψ τ hℓprime)
      fd (secondDualModelMap ψ τ ℓprime Wprime)
    rw [hf] at hR ha
    have hfd : fd.val = adjacentRankDualWhittakerFamily F ψ r U u := by
      change translateWhittaker _ _ (firstDualFunction _ _ f.val) _ = _
      rw [hf]
      rfl
    change HasRationalContinuation qF
      (fun s => corankOneIntegral _ abv ν fd.val (secondDualFunction ψ r Wprime.val) s)
      Rd at hRd
    change HasAbsoluteBilateralSpectralExpansion qF
      (corankCoefficientSeries F _ ν fd.val (secondDualFunction ψ r Wprime.val))
      (fun s => corankOneIntegral _ abv ν fd.val (secondDualFunction ψ r Wprime.val) s)
      at had
    rw [hfd] at hRd had
    exact ⟨R, Rd, hR, hRd, ha, had⟩
  choose R Rd hR hRd ha had using hdata
  have hFE : ∀ u : ℝ, C < u →
      GammaFunctionalEquation qF ζ (r + 1)
        (spectralGammaProduct qF F.canonicalTopologicalData.residueCardinality_gt_one G₀ G₁ (u : ℂ))
        (R (u : ℂ)) (Rd (u : ℂ)) := by
    intro u hu
    obtain ⟨ℓu, hℓu, v, hv⟩ := hcoeff (u : ℂ)
    let π := twoBlockSecondDeformedInduced F m h σ (u : ℂ)
    let f := modelMap π ℓu v
    have hf : f.val = U (u : ℂ) := hv
    have hg := (isPairGammaFactor_of_lt (Nat.lt_succ_self r)).mp
      ((isPadicSymmetricGammaFactor_of_le (Nat.le_succ r)).mp (hgamma u hu))
    obtain ⟨ζu, hζu, hall⟩ := hg.2.2.2 ν hν ℓu ℓprime hℓu hℓprime
    obtain rfl := hζu.unique hℓprime hζ
    obtain ⟨S, Sd, hS, hSd, hN⟩ := (hall 0 0 rfl).2 f Wprime
    have hSc := RationalContinuationLinear.continuation_of_eq_on_right hS
      ⟨0, fun s _ => corankOneIntegral_eq_zeroZero F ψ ν μ f.val Wprime.val s⟩
    have hSdc := RationalContinuationLinear.continuation_of_eq_on_right hSd
      ⟨0, fun s _ => corankOneIntegral_eq_zeroZero F (ψ.scale (-1)) ν μ
        (translateWhittaker _ _ (firstDualFunction ψ (r + 1) f.val)
          (blockWeylAt r (r + 1) (Nat.lt_succ_self r)))
        (secondDualFunction ψ r Wprime.val) s⟩
    rw [hf] at hSc hSdc
    have he : S = R (u : ℂ) := hSc.unique F.canonicalTopologicalData.residueCardinality_gt_one (hR _)
    have hed : Sd = Rd (u : ℂ) := hSdc.unique F.canonicalTopologicalData.residueCardinality_gt_one (hRd _)
    simpa only [he, hed] using hN
  have hclears : ∀ u : ℝ, C < u → ∃ L : LaurentPolynomial ℂ,
      spectralClearingKernel qF P₀ P₁ (u : ℂ) •
        corankCoefficientFamily F ψ ν Wprime.val U (u : ℂ) =
          BilateralLaurentSeries.ofLaurentPolynomial L := by
    intro u hu
    obtain ⟨ℓu, hℓu, v, hv⟩ := hcoeff (u : ℂ)
    obtain ⟨L, hL⟩ := hclear u hu ℓu hℓu v
    rw [hv] at hL
    exact ⟨L, hL.symm⟩
  have hN := gammaFE_spectralProduct_at_zero F.canonicalTopologicalData.residueCardinality_gt_one
    G₀ G₁ P₀ P₁ hP hae hade hR hRd ha had C hclears hFE
  refine ⟨R 0, Rd 0, ?_, ?_, hN⟩
  · simpa only [I, hzero] using hR 0
  · apply RationalContinuationLinear.continuation_of_eq_on_right (hRd 0)
    refine ⟨0, fun s _ => ?_⟩
    change dualUnequalRankModelIntegralAt _ 0 0 rfl ψ abv ν μ
      _ τ ℓ₀ ℓprime W₀ Wprime s = Id 0 s
    unfold dualUnequalRankModelIntegralAt
    rw [← hzero]
    exact (corankOneIntegral_eq_zeroZero F (ψ.scale (-1)) ν μ _ _ s).symm

end Langlands.RankinSelberg.Padic
