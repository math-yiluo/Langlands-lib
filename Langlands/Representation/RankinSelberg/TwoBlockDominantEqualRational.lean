import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualNumerators
import Langlands.Representation.RankinSelberg.TwoBlockDominantCoefficientContinuation
import Langlands.Representation.RankinSelberg.EqualRankAnalyticProof
import Langlands.HarmonicAnalysis.RowFourierCompatibilityProof

/-! # Actual rational comparison and L clearing at equal rank -/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  LaurentPolynomial TwoBlockLowerUnipotentQuotient TwoBlockDominantRectangular LocalFactor
open HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance equalRationalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance equalRationalValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance equalRationalLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance equalRationalT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance equalRationalSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance equalRationalMeasurable : MeasurableSpace F.Carrier := borel _
local instance equalRationalBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance equalRationalDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance equalRationalGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance equalRationalGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalRationalUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance equalRationalUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalRationalQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance equalRationalQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local instance equalRationalReverseAdd : ∀ i : Fin 2, AddCommGroup (W i.rev) :=
  fun i => hadd i.rev
local instance equalRationalReverseModule : ∀ i : Fin 2, Module ℂ (W i.rev) :=
  fun i => hmod i.rev

local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V)
  (lambda : glFunctionals ψ t π)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (hσ : ∀ i, IsSmooth (σ i))
  (J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
  (μN : Measure (LeftUnipotentQuotient t F.Carrier))
  (μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
  (μB : Measure (LeftUnipotentQuotient (m 1) F.Carrier))

/-- Actual original and reversed rational integrals, with both complete block
certificates, uniform finite clearing and the intrinsic L bound. -/
def EqualTwoBlockRationalComparison : Prop :=
  let E := reversedDualSectionEquiv F h σ hσ
  let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
  let ellD := fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev)
  let JD := transportedSecondDualFunctional ψ (TwoBlockJacquet.inducedRep F h σ) E J
  let q := equalResidueCardinalityUnit F
  ∃ (ζ₁ c₁ ζ₂ c₂ : ℂˣ) (d₁ d₂ : ℤ) (P₁ P₁D P₂ P₂D : Polynomial ℂ),
    EqualFirstBlockFactorCertificate F h ψ ν π lambda σ ell μA ζ₁ c₁ d₁ P₁ P₁D ∧
    EqualFirstBlockFactorCertificate F (reverse_sum h) (ψ.scale (-1))
      (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
      (firstDualFunctional ψ π lambda) σD ellD μB ζ₂ c₂ d₂ P₂D P₂ ∧
    (∀ (f : TwoBlockJacquet.Sections F h σ)
      (Wtest : (coefficientModel π lambda).toSubmodule)
      (Φ Φhat : SchwartzBruhat (Fin (t + 1) → F.Carrier)),
      IsRowFourierPair ψ ν.val Φ Φhat →
      ∃ R RD : RationalFunctions,
        HasRationalContinuation qF
          (fun s => equalRankIntegral ψ abv μN Wtest.val
            (modelMap (TwoBlockJacquet.inducedRep F h σ) J f).val Φ s) R ∧
        HasRationalContinuation qF
          (fun s => equalRankIntegral (ψ.scale (-1)) abv μN
            (firstDualModelMap ψ π lambda Wtest).val
            (modelMap (TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)).val
            Φhat s) RD ∧
        RationalReflection.subst q⁻¹
            (laurentToRatFunc (P₁D * P₂D).toLaurent * RD) =
          laurentToRatFunc
              (↑(clearedProductMultiplierUnit q (ζ₁ ^ t * c₁) d₁
                (ζ₂ ^ t * c₂) d₂) : LaurentPolynomial ℂ) *
            laurentToRatFunc (P₁ * P₂).toLaurent * R) ∧
    EqualModelFiniteClearing F ψ μN π (TwoBlockJacquet.inducedRep F h σ)
      lambda J (P₁ * P₂) ∧
    ∀ P : Polynomial ℂ,
      IsEqualRankLPolynomial qF ψ abv μN π (TwoBlockJacquet.inducedRep F h σ) P →
      ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * (P₁ * P₂) = Q * P

set_option maxHeartbeats 1600000 in
/-- Published convergence and rationality turn the actual finite numerators
into rational identities; model surjectivity gives the full intrinsic L bound. -/
theorem equalTwoBlockRationalComparison_of_numerators
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    (hμN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μN)
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hσtype : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hlambda : lambda.val ≠ 0) (hJ0 : J.val ≠ 0)
    (hnum : EqualTwoBlockFiniteNumerators F h ψ ν π lambda σ ell hσ J μN μA μB) :
    EqualTwoBlockRationalComparison F h ψ ν π lambda σ ell hσ J μN μA μB := by
  let E := reversedDualSectionEquiv F h σ hσ
  let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
  let JD := transportedSecondDualFunctional ψ (TwoBlockJacquet.inducedRep F h σ) E J
  let q := equalResidueCardinalityUnit F
  obtain ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D,
    hcert₁, hcert₂, hfinite⟩ := hnum
  have hInd := lowerInduced_inverseWhittakerType F h ψ σ hσtype
  have hAn := equalRankAnalytic F F.canonicalTopologicalData t ψ μN hμN
    V (TwoBlockJacquet.Sections F h σ) π (TwoBlockJacquet.inducedRep F h σ)
    hπ hInd lambda J hlambda hJ0
  have hπD : IsOfWhittakerType t (standardCharacter (ψ.scale (-1)) t)
      (inverseTransposePullback π) := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hσD := reversedDualBlocks_whittakerType F σ ψ hσtype
  have hIndD := lowerInduced_inverseWhittakerType F (reverse_sum h)
    (ψ.scale (-1)) σD hσD
  have hAnD := equalRankAnalytic F F.canonicalTopologicalData t (ψ.scale (-1)) μN hμN
    V (TwoBlockJacquet.Sections F (reverse_sum h) σD) (inverseTransposePullback π)
    (TwoBlockJacquet.inducedRep F (reverse_sum h) σD)
    hπD hIndD (firstDualFunctional ψ π lambda) JD
    (firstDualFunctional_ne_zero ψ π hlambda)
    (transportedSecondDualFunctional_ne_zero ψ (TwoBlockJacquet.inducedRep F h σ) E hJ0)
  have hclear : EqualModelFiniteClearing F ψ μN π (TwoBlockJacquet.inducedRep F h σ)
      lambda J (P₁ * P₂) := by
    intro U U' Φ
    obtain ⟨f, hf⟩ := modelMap_surjective (TwoBlockJacquet.inducedRep F h σ) J U'
    obtain ⟨Φhat, hpair⟩ := (rowFourierCompatibility ψ ν.val (t + 1) ν.property).1 Φ
    obtain ⟨N, hN, -⟩ := hfinite f U Φ Φhat hpair
    exact ⟨N, by simpa only [hf] using hN.1⟩
  have hP₁ : P₁ ≠ 0 := by
    have hsum : (m 0 + 1) + (m 1 + 1) = t + 1 := by
      simpa only [Fin.sum_univ_two] using h
    exact (hcert₁.2.2 0 (m 1) (by omega)).1.polynomial_ne_zero
  have hP₂ : P₂ ≠ 0 := by
    have hsum : (m 0 + 1) + (m 1 + 1) = t + 1 := by
      simpa only [Fin.sum_univ_two] using h
    exact (hcert₂.2.2 0 (m 0) (by
      change t = m 1 + (0 + m 0 + 1)
      omega)).2.polynomial_ne_zero
  refine ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D,
    hcert₁, hcert₂, ?_, hclear, ?_⟩
  · intro f Wtest Φ Φhat hpair
    let U' := modelMap (TwoBlockJacquet.inducedRep F h σ) J f
    let UD := firstDualModelMap ψ π lambda Wtest
    let U'D := modelMap (TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)
    obtain ⟨R, hR⟩ := hAn.2.1 Wtest U' Φ
    obtain ⟨RD, hRD⟩ := hAnD.2.1 UD U'D Φhat
    refine ⟨R, RD, hR, hRD, ?_⟩
    have hexp := equalRank_hasBilateralSpectralExpansion F ψ μN Wtest.val U'.val Φ
      (hAn.1 Wtest U' Φ)
    have hexpD := equalRank_hasBilateralSpectralExpansion F (ψ.scale (-1)) μN
      UD.val U'D.val Φhat (hAnD.1 UD U'D Φhat)
    obtain ⟨N, hN, -⟩ := hfinite f Wtest Φ Φhat hpair
    exact reflectedNumerators_rationalIdentity
      F.canonicalTopologicalData.residueCardinality_gt_one q
      (P₁ * P₂).toLaurent (P₁D * P₂D).toLaurent
      (clearedProductMultiplierUnit q (ζ₁ ^ t * c₁) d₁ (ζ₂ ^ t * c₂) d₂) R RD
      hexp hexpD ⟨N, hN⟩ hR hRD
  · intro P hP
    exact equalModelFiniteClearing_polynomialDivisibility F ψ μN π
      (TwoBlockJacquet.inducedRep F h σ) lambda J hπ hInd hlambda hJ0
      P (P₁ * P₂) (mul_ne_zero hP₁ hP₂) hP hclear

omit σ ell hσ J μN μA μB in
/-- Above a common real opposite-twist bound, actual ordinary Jacquet
functionals give the rational comparison and intrinsic L bound. -/
theorem exists_equalTwoBlockRationalComparison
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 0))]
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 1))]
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hlambda : lambda.val ≠ 0)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell0 : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (hell0 : ∀ i, (ell0 i).val ≠ 0) :
    ∃ Cbound : ℝ, ∀ u : ℝ, Cbound < u →
      let σu := twoBlockOppositeTwistBlocks F m τ u
      let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
      let hσu : ∀ i, IsSmooth (σu i) := fun i =>
        ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i)).1.1
      let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
      (∀ f : TwoBlockJacquet.Sections F h σu,
        TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ell0 i).val) μR f) ∧
      ∃ Ju : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σu),
        Ju.val ≠ 0 ∧
        (∀ (f : TwoBlockJacquet.Sections F h σu)
          (g : GeneralLinear (t + 1) F.Carrier),
          Ju.val (TwoBlockJacquet.inducedRep F h σu g f) =
            TwoBlockJacquet.jacquetFunction ψ (fun i => (ellu i).val) μR f g) ∧
        ∀ (μN : Measure (LeftUnipotentQuotient t F.Carrier))
          (μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
          (μB : Measure (LeftUnipotentQuotient (m 1) F.Carrier)),
          IsCompatible (upperUnipotent (t + 1) F.Carrier)
            (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μN →
          IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
            (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) μA →
          IsCompatible (upperUnipotent (m 1 + 1) F.Carrier)
            (generalLinearHaar F.Carrier (m 1)) (unipotentHaar F.Carrier (m 1)) μB →
          EqualTwoBlockRationalComparison F h ψ ν π lambda σu ellu hσu Ju μN μA μB := by
  obtain ⟨Cbound, hCbound⟩ := exists_equalTwoBlockFiniteNumerators F h ψ ν π lambda
    hπ hlambda τ hτ ell0 hell0
  refine ⟨Cbound, fun u hu => ?_⟩
  dsimp only
  obtain ⟨habs, Ju, hJu0, hJu, hnum⟩ := hCbound u hu
  refine ⟨habs, Ju, hJu0, hJu, ?_⟩
  intro μN μA μB hμN hμA hμB
  exact equalTwoBlockRationalComparison_of_numerators F h ψ ν π lambda
    (twoBlockOppositeTwistBlocks F m τ u)
    (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i))
    (fun i => ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2
      (hτ i)).1.1)
    Ju μN μA μB hμN hπ
    (fun i => (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i))
    hlambda hJu0 (hnum μN μA μB hμN hμA hμB)

end Langlands.RankinSelberg.DominantRankTransport
