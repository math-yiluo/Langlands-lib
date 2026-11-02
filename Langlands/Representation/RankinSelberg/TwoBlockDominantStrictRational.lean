import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictFiniteNumerators
import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictContinuation

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  LaurentPolynomial TwoBlockLowerUnipotentQuotient TwoBlockDominantRectangular LocalFactor
open HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance strictRationalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance strictRationalValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance strictRationalLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance strictRationalT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance strictRationalSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance strictRationalMeasurable : MeasurableSpace F.Carrier := borel _
local instance strictRationalBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance strictRationalGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance strictRationalGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictRationalUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance strictRationalUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictRationalQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance strictRationalQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

variable {t r : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local instance strictRationalReverseAdd : ∀ i : Fin 2, AddCommGroup (W i.rev) :=
  fun i => hadd i.rev
local instance strictRationalReverseModule : ∀ i : Fin 2, Module ℂ (W i.rev) :=
  fun i => hmod i.rev

local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable (htr : t < r) (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (lambda : glFunctionals ψ r π)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (hσ : ∀ i, IsSmooth (σ i))
  (J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
  (μN : Measure (LeftUnipotentQuotient t F.Carrier))
  (μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
  (μB : Measure (LeftUnipotentQuotient (m 1) F.Carrier))

/-- Actual strict original and reversed rational integrals, with retained
complete block certificates, uniform clearing and every intrinsic L bound. -/
def StrictTwoBlockRationalComparison : Prop :=
  let E := reversedDualSectionEquiv F h σ hσ
  let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
  let ellD := fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev)
  let JD := transportedSecondDualFunctional ψ (TwoBlockJacquet.inducedRep F h σ) E J
  let q := strictResidueCardinalityUnit F
  ∃ (ζ₁ c₁ ζ₂ c₂ : ℂˣ) (d₁ d₂ : ℤ) (P₁ P₁D P₂ P₂D : Polynomial ℂ),
    StrictFirstBlockFactorCertificate F h htr ψ ν π lambda σ ell μA ζ₁ c₁ d₁ P₁ P₁D ∧
    StrictFirstBlockFactorCertificate F (reverse_sum h) htr (ψ.scale (-1))
      (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
      (firstDualFunctional ψ π lambda) σD ellD μB ζ₂ c₂ d₂ P₂D P₂ ∧
    (∀ (j k : ℕ) (hr : r = t + (j + k + 1))
      (f : TwoBlockJacquet.Sections F h σ)
      (Wtest : (coefficientModel π lambda).toSubmodule),
      ∃ R RD : RationalFunctions,
        HasRationalContinuation qF
          (unequalRankIntegralAt j k hr ψ abv μN
            (rectangularMeasure ν.val j (t + 1)) Wtest.val
            (modelMap (TwoBlockJacquet.inducedRep F h σ) J f).val) R ∧
        HasRationalContinuation qF
          (unequalRankIntegralAt k j (by omega) (ψ.scale (-1)) abv μN
            (rectangularMeasure ν.val k (t + 1)) (reversedDualTest hr ψ Wtest.val)
            (modelMap (TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)).val) RD ∧
        RationalReflection.subst q⁻¹
            (laurentToRatFunc (P₁D * P₂D).toLaurent * RD) =
          laurentToRatFunc
              (↑(clearedProductMultiplierUnit q (ζ₁ ^ r * c₁) d₁
                (ζ₂ ^ r * c₂) d₂) : LaurentPolynomial ℂ) *
            laurentToRatFunc (P₁ * P₂).toLaurent * R) ∧
    (∀ (j k : ℕ) (hr : r = t + (j + k + 1))
      (U : (coefficientModel π lambda).toSubmodule)
      (U' : (coefficientModel (TwoBlockJacquet.inducedRep F h σ) J).toSubmodule),
      ∃ N : LaurentPolynomial ℂ,
        ofLaurentPolynomial N = (P₁ * P₂).toLaurent •
          strictSliceCoefficient F hr ψ μN ν.val U.val U'.val) ∧
    ∀ (j k : ℕ) (hr : r = t + (j + k + 1)) (P : Polynomial ℂ),
      IsNormalizedGenerator
        (unequalRankZetaValuesAt j k hr qF ψ abv μN
          (rectangularMeasure ν.val j (t + 1)) π (TwoBlockJacquet.inducedRep F h σ)) P →
      ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * (P₁ * P₂) = Q * P

set_option maxHeartbeats 1600000 in
/-- Actual spectral expansions turn the finite numerators into rational
identities. Surjectivity onto the fixed induced model gives the intrinsic
L-polynomial bound at every complementary row. -/
theorem strictTwoBlockRationalComparison_of_numerators
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    (hμN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μN)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσtype : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hlambda : lambda.val ≠ 0) (hJ0 : J.val ≠ 0)
    (hnum : StrictTwoBlockFiniteNumerators F h htr ψ ν π lambda σ ell hσ J μN μA μB) :
    StrictTwoBlockRationalComparison F h htr ψ ν π lambda σ ell hσ J μN μA μB := by
  let E := reversedDualSectionEquiv F h σ hσ
  let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
  let JD := transportedSecondDualFunctional ψ (TwoBlockJacquet.inducedRep F h σ) E J
  let q := strictResidueCardinalityUnit F
  obtain ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D,
    hcert₁, hcert₂, hfinite⟩ := hnum
  have hInd := lowerInduced_inverseWhittakerType F h ψ σ hσtype
  have hπD := isOfWhittakerType_firstDual ψ π hπ
  have hσD := reversedDualBlocks_whittakerType F σ ψ hσtype
  have hIndD := lowerInduced_inverseWhittakerType F (reverse_sum h)
    (ψ.scale (-1)) σD hσD
  have hclear : ∀ (j k : ℕ) (hr : r = t + (j + k + 1))
      (U : (coefficientModel π lambda).toSubmodule)
      (U' : (coefficientModel (TwoBlockJacquet.inducedRep F h σ) J).toSubmodule),
      ∃ N : LaurentPolynomial ℂ,
        ofLaurentPolynomial N = (P₁ * P₂).toLaurent •
          strictSliceCoefficient F hr ψ μN ν.val U.val U'.val := by
    intro j k hr U U'
    obtain ⟨f, hf⟩ := modelMap_surjective (TwoBlockJacquet.inducedRep F h σ) J U'
    obtain ⟨N, hN, -⟩ := hfinite j k hr f U
    exact ⟨N, by simpa only [hf] using hN.1⟩
  have hP₁ : P₁ ≠ 0 := by
    have hblock : m 0 < r := lt_trans (firstBlock_lt_total h) htr
    exact (hcert₁.2.2 0 (r - m 0 - 1) (by omega)).1.polynomial_ne_zero
  have hP₂ : P₂ ≠ 0 := by
    have hsum : (m 0 + 1) + (m 1 + 1) = t + 1 := by
      simpa only [Fin.sum_univ_two] using h
    have hblock : m 1 < r := by omega
    exact (hcert₂.2.2 0 (r - m 1 - 1) (by
      change r = m 1 + (0 + (r - m 1 - 1) + 1)
      omega)).2.polynomial_ne_zero
  refine ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D,
    hcert₁, hcert₂, ?_, hclear, ?_⟩
  · intro j k hr f Wtest
    let U' := modelMap (TwoBlockJacquet.inducedRep F h σ) J f
    let UD := translatedFirstDualModelEquiv ψ π lambda (rightWeyl hr) Wtest
    let U'D := modelMap (TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)
    obtain ⟨hexp, R, hR⟩ := strictCoefficient_continuationData F hr ψ μN ν.val π
      (TwoBlockJacquet.inducedRep F h σ) lambda J hμN hπ hInd hlambda hJ0 Wtest U'
    obtain ⟨hexpD, RD, hRD⟩ := strictCoefficient_continuationData F
      (by omega : r = t + (k + j + 1)) (ψ.scale (-1)) μN ν.val
      (inverseTransposePullback π) (TwoBlockJacquet.inducedRep F (reverse_sum h) σD)
      (firstDualFunctional ψ π lambda) JD hμN hπD hIndD
      (firstDualFunctional_ne_zero ψ π hlambda)
      (transportedSecondDualFunctional_ne_zero ψ (TwoBlockJacquet.inducedRep F h σ) E hJ0)
      UD U'D
    refine ⟨R, RD, hR, hRD, ?_⟩
    obtain ⟨N, hN, -⟩ := hfinite j k hr f Wtest
    exact reflectedNumerators_rationalIdentity
      F.canonicalTopologicalData.residueCardinality_gt_one q
      (P₁ * P₂).toLaurent (P₁D * P₂D).toLaurent
      (clearedProductMultiplierUnit q (ζ₁ ^ r * c₁) d₁ (ζ₂ ^ r * c₂) d₂) R RD
      hexp hexpD ⟨N, hN⟩ hR hRD
  · intro j k hr P hP
    exact strictCoefficient_polynomialDivisibility F hr ψ μN ν.val π
      (TwoBlockJacquet.inducedRep F h σ) lambda J hπ hInd hlambda hJ0
      P (P₁ * P₂) (mul_ne_zero hP₁ hP₂) hP (hclear j k hr)

end Langlands.RankinSelberg.DominantRankTransport
