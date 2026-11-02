import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictSecondBlock

/-! # Actual finite numerators at strictly dominant rank -/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  LaurentPolynomial TwoBlockLowerUnipotentQuotient TwoBlockDominantRectangular
open HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance strictFiniteNumeratorTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance strictFiniteNumeratorValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance strictFiniteNumeratorLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance strictFiniteNumeratorT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance strictFiniteNumeratorSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance strictFiniteNumeratorMeasurable : MeasurableSpace F.Carrier := borel _
local instance strictFiniteNumeratorBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance strictFiniteNumeratorGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance strictFiniteNumeratorGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictFiniteNumeratorUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance strictFiniteNumeratorUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictFiniteNumeratorQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance strictFiniteNumeratorQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

variable {t r : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local instance strictFiniteNumeratorLowerMeasurable :
    MeasurableSpace (LowerQuotient h F.Carrier) := borel _
local instance strictFiniteNumeratorLowerBorel :
    BorelSpace (LowerQuotient h F.Carrier) := ⟨rfl⟩
local instance strictFiniteNumeratorLowerDualMeasurable :
    MeasurableSpace (LowerQuotient (reverse_sum h) F.Carrier) := borel _
local instance strictFiniteNumeratorLowerDualBorel :
    BorelSpace (LowerQuotient (reverse_sum h) F.Carrier) := ⟨rfl⟩

local instance strictFiniteNumeratorReverseAdd : ∀ i : Fin 2, AddCommGroup (W i.rev) :=
  fun i => hadd i.rev
local instance strictFiniteNumeratorReverseModule : ∀ i : Fin 2, Module ℂ (W i.rev) :=
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

variable (hσ : ∀ i, IsSmooth (σ i))
  (J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
  (μN : Measure (LeftUnipotentQuotient t F.Carrier))
  (μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
  (μB : Measure (LeftUnipotentQuotient (m 1) F.Carrier))

/-- Both full first-block certificates and one finite numerator for every
actual coefficient, uniformly over all complementary row pairs. -/
def StrictTwoBlockFiniteNumerators : Prop :=
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
    ∀ (j k : ℕ) (hr : r = t + (j + k + 1))
      (f : TwoBlockJacquet.Sections F h σ)
      (Wtest : (coefficientModel π lambda).toSubmodule),
      let a := strictSliceCoefficient F hr ψ μN ν.val Wtest.val
        (modelMap (TwoBlockJacquet.inducedRep F h σ) J f).val
      let aD := strictDualSliceCoefficient F hr ψ μN ν.val Wtest.val
        (modelMap (TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)).val
      ∃! R : LaurentPolynomial ℂ,
        ofLaurentPolynomial R = (P₁ * P₂).toLaurent • a ∧
        ofLaurentPolynomial (laurentReflection q R) =
          (laurentReflection q
            (↑(clearedProductMultiplierUnit q (ζ₁ ^ r * c₁) d₁
              (ζ₂ ^ r * c₂) d₂)⁻¹ : LaurentPolynomial ℂ) *
                (P₁D * P₂D).toLaurent) • aD

set_option maxHeartbeats 1600000 in
/-- The two actual first-block laws and the proved lower Fourier identity
supply finite numerators. All factor witnesses precede every row and test. -/
theorem strictTwoBlockFiniteNumerators_of_laws
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    (hμN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μN)
    (hπ : IsSmooth π)
    (hLaws : StrictTwoSidedFirstBlockLaws F h htr ψ ν π lambda σ hσ ell J μN μA μB) :
    StrictTwoBlockFiniteNumerators F h htr ψ ν π lambda σ ell hσ J μN μA μB := by
  let E := reversedDualSectionEquiv F h σ hσ
  let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
  let ellD := fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev)
  let JD := transportedSecondDualFunctional ψ (TwoBlockJacquet.inducedRep F h σ) E J
  let q := strictResidueCardinalityUnit F
  obtain ⟨hOriginal, hReversed⟩ := hLaws
  obtain ⟨ζ₁, c₁, d₁, P₁, P₁D, hCert₁, hFirst⟩ := hOriginal
  obtain ⟨ζ₂, c₂, d₂, P₂D, P₂, hCert₂, hSecond⟩ := hReversed
  refine ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D, hCert₁, hCert₂, ?_⟩
  intro j k hr f Wtest
  dsimp only
  let WtestD := translatedFirstDualModelEquiv ψ π lambda (rightWeyl hr) Wtest
  let a := strictSliceCoefficient F hr ψ μN ν.val Wtest.val
    (modelMap (TwoBlockJacquet.inducedRep F h σ) J f).val
  let aD := strictDualSliceCoefficient F hr ψ μN ν.val Wtest.val
    (modelMap (TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)).val
  let b : BilateralLaurentSeries :=
    TwoBlockDominantRectangular.kernelSliceCoefficient ν.val ell f Wtest.val μN hr
  let bD : BilateralLaurentSeries :=
    reversedDualSliceCoefficient F h σ hσ ψ ell hr f Wtest.val ν.val μN
  have hbD : bD = (TwoBlockDominantRectangular.kernelSliceCoefficient ν.val ellD
      (E f) WtestD.val μN (by omega : r = t + (k + j + 1)) :
        BilateralLaurentSeries) := by
    rfl
  have hFirst' :
      Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₁D • b =
        (C ((ζ₁ ^ r * c₁ : ℂˣ) : ℂ) * T d₁ * P₁.toLaurent) • a := by
    dsimp only [q, a, b]
    simpa only [coe_strictResidueCardinalityUnit, Units.val_mul,
      Units.val_pow_eq_pow_val] using hFirst j k hr f Wtest
  have hSecond' :
      Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₂ • bD =
        (C ((ζ₂ ^ r * c₂ : ℂˣ) : ℂ) * T d₂ * P₂D.toLaurent) • aD := by
    rw [hbD]
    simpa only [q, aD, strictDualSliceCoefficient,
      negatedSelfDualHaar_val, coe_strictResidueCardinalityUnit, Units.val_mul,
      Units.val_pow_eq_pow_val, WtestD, translatedFirstDualModelEquiv_val,
      reversedDualTest] using hSecond k j (by omega) (E f) WtestD
  exact twoBlock_strictInducedCoefficient_numerators F h ψ σ hσ ell hr π hπ lambda J JD
    μN ν.val inferInstance hμN f Wtest (ζ₁ ^ r * c₁) d₁ (ζ₂ ^ r * c₂) d₂
    P₁ P₁D P₂ P₂D (by dsimp only [q, a, b] at hFirst'; exact hFirst')
      (by dsimp only [q, aD, bD] at hSecond'; exact hSecond')

omit σ ell hσ J μN μA μB in
/-- Above one real bound, a nonzero ordinary Jacquet functional supplies both
complete block certificates and finite numerators uniformly in the compatible
quotient measures. The independently owned analytic first-block statement is an explicit premise. -/
theorem exists_strictTwoBlockFiniteNumerators
    (H : TwoBlockDominantFirstBlockLaurentIdentityStatement.{uF,uV,uW})
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 0))]
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 1))]
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
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
          StrictTwoBlockFiniteNumerators F h htr ψ ν π lambda σu ellu hσu Ju μN μA μB := by
  obtain ⟨Cbound, hCbound⟩ := exists_strictTwoSidedFirstBlockLaws F h htr ψ ν τ ell0
    π lambda H hπ hlambda hτ hell0
  refine ⟨Cbound, fun u hu => ?_⟩
  dsimp only
  obtain ⟨habs, Ju, hJu0, hJu, hLaws⟩ := hCbound u hu
  refine ⟨habs, Ju, hJu0, hJu, ?_⟩
  intro μN μA μB hμN hμA hμB
  exact strictTwoBlockFiniteNumerators_of_laws F h htr ψ ν π lambda
    (twoBlockOppositeTwistBlocks F m τ u)
    (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i))
    (fun i => ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2
      (hτ i)).1.1)
    Ju μN μA μB hμN hπ.1.1
    (hLaws μN μA μB hμN hμA hμB)

end Langlands.RankinSelberg.DominantRankTransport
