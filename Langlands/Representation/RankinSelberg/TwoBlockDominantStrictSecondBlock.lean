import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictFirstBlock

/-! # Conditional two-sided first-block laws at strictly dominant rank -/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  LaurentPolynomial TwoBlockDominantRectangular TwoBlockLowerUnipotentQuotient

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance strictSecondBlockTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance strictSecondBlockValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance strictSecondBlockLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance strictSecondBlockT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance strictSecondBlockSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance strictSecondBlockMeasurable : MeasurableSpace F.Carrier := borel _
local instance strictSecondBlockBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance strictSecondBlockGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance strictSecondBlockGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictSecondBlockUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance strictSecondBlockUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictSecondBlockQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance strictSecondBlockQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

variable {t r : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local instance strictSecondBlockReverseAdd : ∀ i : Fin 2, AddCommGroup (W i.rev) :=
  fun i => hadd i.rev
local instance strictSecondBlockReverseModule : ∀ i : Fin 2, Module ℂ (W i.rev) :=
  fun i => hmod i.rev

variable (htr : t < r) (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
  (ell0 : ∀ i, glInverseFunctionals ψ (m i) (τ i))

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (lambda : glFunctionals ψ r π)

set_option maxHeartbeats 1600000 in
/-- Above one bound the actual reversed first-block law holds for the fixed
transported second-dual functional, at the original real deformation parameter. -/
theorem exists_reversedStrictFirstBlockBound
    (H : TwoBlockDominantFirstBlockLaurentIdentityStatement.{uF,uV,uW})
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 1))]
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
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
          StrictFirstBlockCoefficientLaw F (reverse_sum h) htr (ψ.scale (-1))
            (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
            (firstDualFunctional ψ π lambda) σD ellD JD μN μB := by
  let τD := fun i : Fin 2 => inverseTransposePullback (τ i.rev)
  let ellD0 := fun i : Fin 2 => secondDualFunctional ψ (τ i.rev) (ell0 i.rev)
  have hπD : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r)
      (inverseTransposePullback π) := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hτD := reversedDualBlocks_whittakerType F τ ψ hτ
  obtain ⟨Cdual, hCdual⟩ := exists_strictFirstBlockBound_forOrdinaryFunctional F
    (reverse_sum h) htr (ψ.scale (-1)) (negatedSelfDualHaar F ψ ν)
    (inverseTransposePullback π) (firstDualFunctional ψ π lambda) H hπD
    (firstDualFunctional_ne_zero ψ π hlambda) τD hτD ellD0
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

/-- The two first-block equations for the same fixed dual section,
with one witness tuple for every complementary row pair. -/
def StrictTwoSidedFirstBlockLaws
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
  StrictFirstBlockCoefficientLaw F h htr ψ ν π lambda σ ell J μN μA ∧
  StrictFirstBlockCoefficientLaw F (reverse_sum h) htr (ψ.scale (-1))
    (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
    (firstDualFunctional ψ π lambda) σD ellD JD μN μB

set_option maxHeartbeats 1600000 in
/-- Above one real bound a nonzero ordinary Jacquet functional satisfies
both actual first-block equations, conditional on the analytic theorem,
uniformly over all three compatible quotient measures. -/
theorem exists_strictTwoSidedFirstBlockLaws
    (H : TwoBlockDominantFirstBlockLaurentIdentityStatement.{uF,uV,uW})
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 0))]
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 1))]
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
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
          StrictTwoSidedFirstBlockLaws F h htr ψ ν π lambda σu hσu ellu Ju μN μA μB := by
  obtain ⟨Coriginal, hOriginal⟩ := exists_strictFirstBlockCoefficientLaw F h htr ψ ν π
    lambda H hπ hlambda τ hτ ell0 hell0
  obtain ⟨Creversed, hReversed⟩ := exists_reversedStrictFirstBlockBound F h htr ψ ν τ
    ell0 π lambda H hπ hlambda hτ hell0
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
  exact ⟨hFirst μN μA hμN hμA, hReversed u hur J hJ μN μB hμN hμB⟩

end Langlands.RankinSelberg.DominantRankTransport
