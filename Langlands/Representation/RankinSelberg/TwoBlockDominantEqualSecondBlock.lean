import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualFirstBlock
import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualDuality
import Langlands.Representation.RankinSelberg.TwoBlockDominantDualJacquet

/-! # The actual reversed first-block law at equal rank -/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  LaurentPolynomial TwoBlockDominantRectangular TwoBlockLowerUnipotentQuotient

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance equalSecondBlockTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance equalSecondBlockValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance equalSecondBlockLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance equalSecondBlockT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance equalSecondBlockSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance equalSecondBlockMeasurable : MeasurableSpace F.Carrier := borel _
local instance equalSecondBlockBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance equalSecondBlockGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance equalSecondBlockGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalSecondBlockUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance equalSecondBlockUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalSecondBlockQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance equalSecondBlockQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

/-- Every complex determinant power is one on the long Weyl representative. -/
theorem determinantComplexPower_weylLong (n : ℕ) (s : ℂ) :
    F.canonicalTopologicalData.determinantComplexPower n s
      (weylLong n F.Carrier) = 1 := by
  apply Units.ext
  rw [PadicField.TopologicalData.determinantComplexPower_apply,
    PadicField.TopologicalData.determinantNorm_coe]
  have hw := TwoBlockFirstBlockLaurent.abv_det_weylLong
    (normalizedAbsoluteValue F.canonicalTopologicalData) n
  change F.canonicalTopologicalData.normalizedAbs
    (determinant (weylLong n F.Carrier) : F.Carrier) = 1 at hw
  simp only [hw, Complex.ofReal_one, Complex.one_cpow, Units.val_one]

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local instance equalSecondBlockReverseAdd : ∀ i : Fin 2, AddCommGroup (W i.rev) :=
  fun i => hadd i.rev
local instance equalSecondBlockReverseModule : ∀ i : Fin 2, Module ℂ (W i.rev) :=
  fun i => hmod i.rev

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
  (ell0 : ∀ i, glInverseFunctionals ψ (m i) (τ i))

/-- Dualizing a deformed block preserves the base dual functional's linear map. -/
theorem secondDual_oppositeTwistFunctional_val (u : ℝ) (i : Fin 2) :
    (secondDualFunctional ψ (twoBlockOppositeTwistBlocks F m τ u i)
      (twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i))).val =
      (secondDualFunctional ψ (τ i) (ell0 i)).val := by
  ext v
  change (ell0 i).val
      (twoBlockOppositeTwistBlocks F m τ u i (weylLong (m i + 1) F.Carrier) v) =
    (ell0 i).val (τ i (weylLong (m i + 1) F.Carrier) v)
  change (ell0 i).val
      ((F.canonicalTopologicalData.determinantComplexPower (m i + 1)
        (if i = 0 then -(u : ℂ) else (u : ℂ))
        (weylLong (m i + 1) F.Carrier) : ℂ) •
        τ i (weylLong (m i + 1) F.Carrier) v) = _
  rw [determinantComplexPower_weylLong, Units.val_one, one_smul]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V)
  (lambda : glFunctionals ψ t π)

/-- The first-block bound also works for any equal block presentation and any
functional realizing the ordinary Jacquet function. -/
theorem exists_equalFirstBlockBound_forOrdinaryFunctional
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 0))]
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hlambda : lambda.val ≠ 0)
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (hell0 : ∀ i, (ell0 i).val ≠ 0) :
    ∃ Cbound : ℝ, ∀ u : ℝ, Cbound < u →
      ∀ (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)),
        σ = twoBlockOppositeTwistBlocks F m τ u →
      ∀ (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)),
        (∀ i, (ell i).val = (ell0 i).val) →
      ∀ (J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ)),
        (∀ (f : TwoBlockJacquet.Sections F h σ)
          (g : GeneralLinear (t + 1) F.Carrier),
          J.val (TwoBlockJacquet.inducedRep F h σ g f) =
            TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val)
              (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f g) →
      ∀ (μN : Measure (LeftUnipotentQuotient t F.Carrier))
        (μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)),
        IsCompatible (upperUnipotent (t + 1) F.Carrier)
          (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μN →
        IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
          (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) μA →
        EqualFirstBlockCoefficientLaw F h ψ ν π lambda σ ell J μN μA := by
  obtain ⟨_, _, _, _, hFirst⟩ :=
    twoBlockFirstBlockLaurentIdentity.{uF,uV,uW} p F ψ ν t m h
  obtain ⟨Cfirst, hCfirst⟩ := hFirst π hπ lambda τ hτ ell0
  refine ⟨Cfirst, fun u hu σ hσ ell hell J hJ μN μA hμN hμA => ?_⟩
  subst σ
  have hellEq : ell = fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i) := by
    funext i
    exact Subtype.ext (hell i)
  subst ell
  let σu := twoBlockOppositeTwistBlocks F m τ u
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
  obtain ⟨_, _, _, _, hLaurent⟩ := hCfirst u hu μN μA hμN hμA
  have hσ0 : IsOfWhittakerType (m 0) (inverseStandardCharacter ψ (m 0)) (σu 0) :=
    (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u 0 _).2
      ((isOfWhittakerType_standard_iff_inverse ψ (τ 0)).1 (hτ 0))
  have heq := unequalRankFunctionalEquation F F.canonicalTopologicalData (m 0) t
    (firstBlock_lt_total h) ψ μA hμA ν.val ν.property V (W 0) π (σu 0)
    hπ hσ0 lambda (ellu 0) hlambda (hell0 0)
  obtain ⟨c, d, hEpsilon⟩ := exists_unequalRankEpsilonEquation_iff.mpr heq
  obtain ⟨ζ, P, Pdual, hζ, hBody, hLaw⟩ := hLaurent c d hEpsilon
  refine ⟨ζ, c, d, P, Pdual, hEpsilon, hζ,
    fun j k hr => ⟨(hBody j k hr).1, (hBody j k hr).2.1⟩, ?_⟩
  intro f Wtest Φ
  have ha := hLaw f Wtest Φ
  change _ = _ at ha
  change _ = _
  rw [← unfoldedJacquetSeries_eq F h ψ σu ellu
    (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) μN J hJ f Wtest.val Φ]
  exact ha

set_option maxHeartbeats 1600000 in
/-- The fixed section equivalence used by the Fourier law also realizes the
transported second-dual functional by the ordinary reversed Jacquet integral. -/
theorem reversedDualSectionEquiv_ordinary
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ : ∀ i, IsSmooth (σ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
    (hJ : ∀ (f : TwoBlockJacquet.Sections F h σ)
      (g : GeneralLinear (t + 1) F.Carrier),
      J.val (TwoBlockJacquet.inducedRep F h σ g f) =
        TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val)
          (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f g) :
    let E := reversedDualSectionEquiv F h σ hσ
    let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
    let ellD := fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev)
    let JD := transportedSecondDualFunctional ψ (TwoBlockJacquet.inducedRep F h σ) E J
    ∀ (fD : TwoBlockJacquet.Sections F (reverse_sum h) σD)
      (g : GeneralLinear (t + 1) F.Carrier),
      JD.val (TwoBlockJacquet.inducedRep F (reverse_sum h) σD g fD) =
        TwoBlockJacquet.jacquetFunction (ψ.scale (-1)) (fun i => (ellD i).val)
          (rectangularMeasure ν.val (m 1 + 1) (m 0 + 1)) fD g := by
  dsimp only
  let E := reversedDualSectionEquiv F h σ hσ
  intro fD g
  have hh := transportedSecondDualFunctional_coefficient ψ
    (TwoBlockJacquet.inducedRep F h σ) E J (E.symm fD)
  have hg := congrArg (fun Z : InverseWhittakerFunctions (ψ.scale (-1)) t => Z.val g) hh
  simp only [E.apply_symm_apply] at hg
  change (transportedSecondDualFunctional ψ (TwoBlockJacquet.inducedRep F h σ) E J).val
    (TwoBlockJacquet.inducedRep F (reverse_sum h)
      (fun i => inverseTransposePullback (σ i.rev)) g fD) =
    J.val (TwoBlockJacquet.inducedRep F h σ
    (weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier g)
    (E.symm fD)) at hg
  rw [hg, hJ]
  have hE := Classical.choose_spec (twoBlockDualSectionJacquet p F t m h W σ hσ)
  obtain ⟨_, _, _, _, _, hjac⟩ := (hE.2.2 ψ ell).2.2 ν.val
  have hFinal := (hjac (E.symm fD) g).symm
  change TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val)
      (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) (E.symm fD)
      (weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier g) =
    TwoBlockJacquet.jacquetFunction (ψ.scale (-1))
      (fun i => (secondDualFunctional ψ (σ i.rev) (ell i.rev)).val)
      (rectangularMeasure ν.val (m 1 + 1) (m 0 + 1)) (E (E.symm fD)) g at hFinal
  simpa only [E.apply_symm_apply] using hFinal

set_option maxHeartbeats 1600000 in
/-- Above one bound the actual reversed first-block law holds for the fixed
transported second-dual functional, at the original real deformation parameter. -/
theorem exists_reversedEqualFirstBlockBound
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 1))]
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hlambda : lambda.val ≠ 0)
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (hell0 : ∀ i, (ell0 i).val ≠ 0) :
    ∃ Cbound : ℝ, ∀ u : ℝ, Cbound < u →
      let σu := twoBlockOppositeTwistBlocks F m τ u
      let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
      let hσu : ∀ i, IsSmooth (σu i) := fun i =>
        ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i)).1.1
      let E := reversedDualSectionEquiv F h σu hσu
      let σD := fun i : Fin 2 => inverseTransposePullback (σu i.rev)
      let ellD := fun i : Fin 2 => secondDualFunctional ψ (σu i.rev) (ellu i.rev)
      ∀ J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σu),
        (∀ (f : TwoBlockJacquet.Sections F h σu)
          (g : GeneralLinear (t + 1) F.Carrier),
          J.val (TwoBlockJacquet.inducedRep F h σu g f) =
            TwoBlockJacquet.jacquetFunction ψ (fun i => (ellu i).val)
              (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f g) →
        let JD := transportedSecondDualFunctional ψ
          (TwoBlockJacquet.inducedRep F h σu) E J
        ∀ (μN : Measure (LeftUnipotentQuotient t F.Carrier))
          (μB : Measure (LeftUnipotentQuotient (m 1) F.Carrier)),
          IsCompatible (upperUnipotent (t + 1) F.Carrier)
            (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μN →
          IsCompatible (upperUnipotent (m 1 + 1) F.Carrier)
            (generalLinearHaar F.Carrier (m 1)) (unipotentHaar F.Carrier (m 1)) μB →
          EqualFirstBlockCoefficientLaw F (reverse_sum h) (ψ.scale (-1))
            (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
            (firstDualFunctional ψ π lambda) σD ellD JD μN μB := by
  let τD := fun i : Fin 2 => inverseTransposePullback (τ i.rev)
  let ellD0 := fun i : Fin 2 => secondDualFunctional ψ (τ i.rev) (ell0 i.rev)
  have hπD : IsOfWhittakerType t (standardCharacter (ψ.scale (-1)) t)
      (inverseTransposePullback π) := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hτD := reversedDualBlocks_whittakerType F τ ψ hτ
  obtain ⟨Cdual, hCdual⟩ := exists_equalFirstBlockBound_forOrdinaryFunctional F
    (reverse_sum h) (ψ.scale (-1)) (negatedSelfDualHaar F ψ ν) τD ellD0
    (inverseTransposePullback π) (firstDualFunctional ψ π lambda) hπD
    (firstDualFunctional_ne_zero ψ π hlambda) hτD
    (fun i => secondDualFunctional_ne_zero ψ (τ i.rev) (hell0 i.rev))
  refine ⟨Cdual, fun u hu => ?_⟩
  dsimp only
  intro J hJ μN μB hμN hμB
  let σu := twoBlockOppositeTwistBlocks F m τ u
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
  let hσu : ∀ i, IsSmooth (σu i) := fun i =>
    ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i)).1.1
  let E := reversedDualSectionEquiv F h σu hσu
  let σD := fun i : Fin 2 => inverseTransposePullback (σu i.rev)
  let ellD := fun i : Fin 2 => secondDualFunctional ψ (σu i.rev) (ellu i.rev)
  let JD := transportedSecondDualFunctional ψ (TwoBlockJacquet.inducedRep F h σu) E J
  have hJD := reversedDualSectionEquiv_ordinary F h ψ ν σu hσu ellu J hJ
  exact hCdual u hu σD (reversedDual_oppositeTwistBlocks F τ u) ellD
    (fun i => secondDual_oppositeTwistFunctional_val F ψ τ ell0 u i.rev)
    JD hJD μN μB hμN hμB

/-- The original first-block equation, the reversed first-block equation
for the same fixed dual section, and its actual lower Fourier law. -/
def EqualTwoSidedFirstBlockLaws
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ : ∀ i, IsSmooth (σ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
    (μN : Measure (LeftUnipotentQuotient t F.Carrier))
    (μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
    (μB : Measure (LeftUnipotentQuotient (m 1) F.Carrier)) : Prop :=
  let E := reversedDualSectionEquiv F h σ hσ
  let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
  let ellD := fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev)
  let JD := transportedSecondDualFunctional ψ (TwoBlockJacquet.inducedRep F h σ) E J
  EqualFirstBlockCoefficientLaw F h ψ ν π lambda σ ell J μN μA ∧
  EqualFirstBlockCoefficientLaw F (reverse_sum h) (ψ.scale (-1))
    (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
    (firstDualFunctional ψ π lambda) σD ellD JD μN μB ∧
  EqualLowerFourierCoefficientLaw F h σ hσ ψ ell ν μN

set_option maxHeartbeats 1600000 in
/-- Above one real bound a nonzero ordinary Jacquet functional satisfies
both actual first-block equations and the fixed-section lower Fourier law,
uniformly over all three compatible quotient measures. -/
theorem exists_equalTwoSidedFirstBlockLaws
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 0))]
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 1))]
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hlambda : lambda.val ≠ 0)
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
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
          EqualTwoSidedFirstBlockLaws F h ψ ν π lambda σu hσu ellu Ju μN μA μB := by
  obtain ⟨Coriginal, hOriginal⟩ := exists_equalFirstBlockCoefficientLaw F h ψ ν π
    lambda hπ hlambda τ hτ ell0 hell0
  obtain ⟨Creversed, hReversed⟩ := exists_reversedEqualFirstBlockBound F h ψ ν τ
    ell0 π lambda hπ hlambda hτ hell0
  refine ⟨max Coriginal Creversed, fun u hu => ?_⟩
  dsimp only
  let σu := twoBlockOppositeTwistBlocks F m τ u
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
  let hσu : ∀ i, IsSmooth (σu i) := fun i =>
    ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i)).1.1
  have huo : Coriginal < u := lt_of_le_of_lt (le_max_left _ _) hu
  have hur : Creversed < u := lt_of_le_of_lt (le_max_right _ _) hu
  obtain ⟨habs, J, hJ0, hJ, hFirst⟩ := hOriginal u huo
  refine ⟨habs, J, hJ0, hJ, ?_⟩
  intro μN μA μB hμN hμA hμB
  refine ⟨hFirst μN μA hμN hμA, ?_, ?_⟩
  · exact hReversed u hur J hJ μN μB hμN hμB
  · exact equalLowerFourierCoefficientLaw F h σu hσu ψ ellu ν μN hμN

end Langlands.RankinSelberg.DominantRankTransport
