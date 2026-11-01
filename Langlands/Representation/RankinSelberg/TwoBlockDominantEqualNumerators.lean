import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualSecondBlock
import Langlands.Representation.RankinSelberg.TwoBlockDominantNumeratorExtraction

/-! # Actual finite numerators at the equal-rank boundary -/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  LaurentPolynomial TwoBlockLowerUnipotentQuotient TwoBlockDominantRectangular
open HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance equalNumeratorTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance equalNumeratorValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance equalNumeratorLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance equalNumeratorT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance equalNumeratorSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance equalNumeratorMeasurable : MeasurableSpace F.Carrier := borel _
local instance equalNumeratorBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance equalNumeratorGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance equalNumeratorGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalNumeratorUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance equalNumeratorUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalNumeratorQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance equalNumeratorQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

/-- The nonzero canonical residue cardinality, as a complex unit. -/
def equalResidueCardinalityUnit : ℂˣ :=
  Units.mk0 (F.canonicalTopologicalData.residueCardinality : ℂ) (by
    have hq : F.canonicalTopologicalData.residueCardinality ≠ 0 :=
      ne_of_gt (lt_trans Nat.zero_lt_one
        F.canonicalTopologicalData.residueCardinality_gt_one)
    exact_mod_cast hq)

@[simp]
theorem coe_equalResidueCardinalityUnit :
    (equalResidueCardinalityUnit F : ℂ) =
      (F.canonicalTopologicalData.residueCardinality : ℂ) := rfl

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local instance equalNumeratorReverseAdd : ∀ i : Fin 2, AddCommGroup (W i.rev) :=
  fun i => hadd i.rev
local instance equalNumeratorReverseModule : ∀ i : Fin 2, Module ℂ (W i.rev) :=
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

/-- The complete first-block factor witnesses, retained before all tests. -/
def EqualFirstBlockFactorCertificate
    (μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
    (ζ c : ℂˣ) (d : ℤ) (P Pdual : Polynomial ℂ) : Prop :=
  UnequalRankEpsilonEquation (firstBlock_lt_total h) qF ψ abv μA ν.val
    π (σ 0) lambda (ell 0) c d ∧
  HasModelMinusOneScalar (σ 0) (ell 0) ζ ∧
  ∀ (j k : ℕ) (hr : t = m 0 + (j + k + 1)),
    IsNormalizedGenerator
      (unequalRankValuesAt j k hr qF ψ abv μA
        (rectangularMeasure ν.val j (m 0 + 1)) π (σ 0) lambda (ell 0)) P ∧
    IsNormalizedGenerator
      (dualUnequalRankRationalValuesAt (firstBlock_lt_total h) j k hr
        qF ψ abv μA ν.val π (σ 0) lambda (ell 0)) Pdual

variable (hσ : ∀ i, IsSmooth (σ i))
  (J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
  (μN : Measure (LeftUnipotentQuotient t F.Carrier))
  (μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
  (μB : Measure (LeftUnipotentQuotient (m 1) F.Carrier))

/-- Both first-block certificates and their actual finite numerator identities.
The reversed first block has original polynomial `P₂D` and dual polynomial `P₂`. -/
def EqualTwoBlockFiniteNumerators : Prop :=
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
    ∀ (f : TwoBlockJacquet.Sections F h σ)
      (Wtest : (coefficientModel π lambda).toSubmodule)
      (Φ Φhat : SchwartzBruhat (Fin (t + 1) → F.Carrier)),
      IsRowFourierPair ψ ν.val Φ Φhat →
      let a : BilateralLaurentSeries :=
        equalRankSliceCoefficient F.canonicalTopologicalData μN ψ Wtest.val
        (modelMap (TwoBlockJacquet.inducedRep F h σ) J f).val Φ
      let aD : BilateralLaurentSeries :=
        equalRankSliceCoefficient F.canonicalTopologicalData μN (ψ.scale (-1))
        (firstDualModelMap ψ π lambda Wtest).val
        (modelMap (TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)).val Φhat
      ∃! R : LaurentPolynomial ℂ,
        ofLaurentPolynomial R = (P₁ * P₂).toLaurent • a ∧
        ofLaurentPolynomial (laurentReflection q R) =
          (laurentReflection q
            (↑(clearedProductMultiplierUnit q (ζ₁ ^ t * c₁) d₁
              (ζ₂ ^ t * c₂) d₂)⁻¹ : LaurentPolynomial ℂ) *
                (P₁D * P₂D).toLaurent) • aD

set_option maxHeartbeats 1600000 in
/-- The actual two-sided laws give finite numerators, with their full factor
certificates common to every section, coefficient and Fourier pair. -/
theorem equalTwoBlockFiniteNumerators_of_laws
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    (hμN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μN)
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hσtype : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hLaws : EqualTwoSidedFirstBlockLaws F h ψ ν π lambda σ hσ ell J μN μA μB) :
    EqualTwoBlockFiniteNumerators F h ψ ν π lambda σ ell hσ J μN μA μB := by
  let E := reversedDualSectionEquiv F h σ hσ
  let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
  let ellD := fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev)
  let JD := transportedSecondDualFunctional ψ (TwoBlockJacquet.inducedRep F h σ) E J
  let q := equalResidueCardinalityUnit F
  obtain ⟨hOriginal, hReversed, hFourier⟩ := hLaws
  obtain ⟨ζ₁, c₁, d₁, P₁, P₁D, hε₁, hζ₁, hP₁, hFirst⟩ := hOriginal
  obtain ⟨ζ₂, c₂, d₂, P₂D, P₂, hε₂, hζ₂, hP₂, hSecond⟩ := hReversed
  refine ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D,
    ⟨hε₁, hζ₁, hP₁⟩, ⟨hε₂, hζ₂, hP₂⟩, ?_⟩
  intro f Wtest Φ Φhat hpair
  dsimp only
  let a : BilateralLaurentSeries :=
    equalRankSliceCoefficient F.canonicalTopologicalData μN ψ Wtest.val
    (modelMap (TwoBlockJacquet.inducedRep F h σ) J f).val Φ
  let WtestD := firstDualModelMap ψ π lambda Wtest
  let fD := modelMap (TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)
  let aD : BilateralLaurentSeries :=
    equalRankSliceCoefficient F.canonicalTopologicalData μN (ψ.scale (-1))
    WtestD.val fD.val Φhat
  let b := equalFirstBlockLowerSeries F h ψ ν π lambda σ ell μN f Wtest Φ
  let bD := equalFirstBlockLowerSeries F (reverse_sum h) (ψ.scale (-1))
    (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
    (firstDualFunctional ψ π lambda) σD ellD μN (E f) WtestD Φhat
  have ha : HasLowerBoundedSupport a :=
    equalRankSliceSupport F F.canonicalTopologicalData t ψ μN hμN V
      (TwoBlockJacquet.Sections F h σ) π (TwoBlockJacquet.inducedRep F h σ)
      hπ (lowerInduced_inverseWhittakerType F h ψ σ hσtype) lambda J Wtest
      (modelMap (TwoBlockJacquet.inducedRep F h σ) J f) Φ
  have hπD : IsOfWhittakerType t (standardCharacter (ψ.scale (-1)) t)
      (inverseTransposePullback π) := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hσD := reversedDualBlocks_whittakerType F σ ψ hσtype
  have haD : HasLowerBoundedSupport aD :=
    equalRankSliceSupport F F.canonicalTopologicalData t (ψ.scale (-1)) μN hμN V
      (TwoBlockJacquet.Sections F (reverse_sum h) σD) (inverseTransposePullback π)
      (TwoBlockJacquet.inducedRep F (reverse_sum h) σD) hπD
      (lowerInduced_inverseWhittakerType F (reverse_sum h) (ψ.scale (-1)) σD hσD)
      (firstDualFunctional ψ π lambda) JD WtestD fD Φhat
  have hFirst' :
      Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₁D • b =
        (C ((ζ₁ ^ t * c₁ : ℂˣ) : ℂ) * T d₁ * P₁.toLaurent) • a := by
    simpa only [q, coe_equalResidueCardinalityUnit, Units.val_mul, Units.val_pow_eq_pow_val]
      using hFirst f Wtest Φ
  have hSecond' :
      Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₂ • bD =
        (C ((ζ₂ ^ t * c₂ : ℂˣ) : ℂ) * T d₂ * P₂D.toLaurent) • aD := by
    simpa only [q, coe_equalResidueCardinalityUnit, Units.val_mul, Units.val_pow_eq_pow_val]
      using hSecond (E f) WtestD Φhat
  have hFourier' (k : ℤ) : bD (-k) = (q : ℂ) ^ (-k) * b k := by
    exact (hFourier f Wtest.val Φ Φhat hpair k).2.1
  exact twoBlock_cleared_numerators q (ζ₁ ^ t * c₁) d₁ (ζ₂ ^ t * c₂) d₂
    ha haD hFirst' hSecond' hFourier'

omit σ ell hσ J μN μA μB in
/-- Above one real bound, a nonzero ordinary Jacquet functional supplies both
complete block certificates and finite numerators uniformly in the compatible
quotient measures. No first-block or Fourier identity is a premise. -/
theorem exists_equalTwoBlockFiniteNumerators
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
          EqualTwoBlockFiniteNumerators F h ψ ν π lambda σu ellu hσu Ju μN μA μB := by
  obtain ⟨Cbound, hCbound⟩ := exists_equalTwoSidedFirstBlockLaws F h ψ ν τ ell0
    π lambda hπ hlambda hτ hell0
  refine ⟨Cbound, fun u hu => ?_⟩
  dsimp only
  obtain ⟨habs, Ju, hJu0, hJu, hLaws⟩ := hCbound u hu
  refine ⟨habs, Ju, hJu0, hJu, ?_⟩
  intro μN μA μB hμN hμA hμB
  exact equalTwoBlockFiniteNumerators_of_laws F h ψ ν π lambda
    (twoBlockOppositeTwistBlocks F m τ u)
    (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i))
    (fun i => ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2
      (hτ i)).1.1)
    Ju μN μA μB hμN hπ
    (fun i => (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i))
    (hLaws μN μA μB hμN hμA hμB)

end Langlands.RankinSelberg.DominantRankTransport
