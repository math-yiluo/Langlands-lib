import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictRational
import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualFactors

/-! # Strict-rank symmetric factors and the L bound on the real ray -/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  Polynomial TwoBlockLowerUnipotentQuotient

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance strictFactorsTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance strictFactorsValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance strictFactorsLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance strictFactorsT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance strictFactorsMeasurable : MeasurableSpace F.Carrier := borel _
local instance strictFactorsBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance strictFactorsGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance strictFactorsGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictFactorsUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance strictFactorsUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictFactorsQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance strictFactorsQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData


variable {t r : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local instance strictFactorsReverseAdd : ∀ i : Fin 2, AddCommGroup (W i.rev) :=
  fun i => hadd i.rev
local instance strictFactorsReverseModule : ∀ i : Fin 2, Module ℂ (W i.rev) :=
  fun i => hmod i.rev

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

omit σ ell hσ J μN μA μB in
/-- Above one real bound, a nonzero ordinary Jacquet functional supplies the
actual rational comparison uniformly in all compatible quotient measures.
The independently owned analytic first-block statement is an explicit premise. -/
theorem exists_strictTwoBlockRationalComparison
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
          StrictTwoBlockRationalComparison F h htr ψ ν π lambda σu ellu hσu Ju μN μA μB := by
  obtain ⟨Cbound, hCbound⟩ := exists_strictTwoBlockFiniteNumerators F h htr ψ ν π lambda
    H hπ hlambda τ hτ ell0 hell0
  refine ⟨Cbound, fun u hu => ?_⟩
  dsimp only
  obtain ⟨habs, Ju, hJu0, hJu, hnum⟩ := hCbound u hu
  refine ⟨habs, Ju, hJu0, hJu, ?_⟩
  intro μN μA μB hμN hμA hμB
  exact strictTwoBlockRationalComparison_of_numerators F h htr ψ ν π lambda
    (twoBlockOppositeTwistBlocks F m τ u)
    (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i))
    (fun i => ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2
      (hτ i)).1.1)
    Ju μN μA μB hμN hπ
    (fun i => (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i))
    hlambda hJu0 (hnum μN μA μB hμN hμA hμB)

/-- The full symmetric certificates attached to the retained first-block
monomial and polynomial pair. -/
def StrictFirstBlockSymmetricFactors (c : ℂˣ) (d : ℤ)
    (P Pdual : Polynomial ℂ) : Prop :=
  IsPadicSymmetricEpsilonFactor F ψ ν.val π (σ 0) (c, d) ∧
  IsPadicSymmetricLPolynomial F ψ ν.val π (σ 0) P ∧
  IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
    (inverseTransposePullback π) (inverseTransposePullback (σ 0)) Pdual ∧
  IsPadicSymmetricGammaFactor F ψ ν.val π (σ 0)
    (rationalGammaExpression (LocalFactor.residueReflection F) c d P Pdual)

omit ell in
/-- No generator or epsilon data are replaced when a retained first-block
certificate is upgraded to symmetric factors. -/
theorem StrictFirstBlockFactorCertificate.symmetricFactors
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hlambda : lambda.val ≠ 0)
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (hell : (ell 0).val ≠ 0)
    {μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)}
    (hμA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) μA)
    {ζ c : ℂˣ} {d : ℤ} {P Pdual : Polynomial ℂ}
    (hcert : StrictFirstBlockFactorCertificate F h htr ψ ν π lambda σ ell μA
      ζ c d P Pdual) :
    StrictFirstBlockSymmetricFactors F ψ ν π σ c d P Pdual :=
  symmetricFactors_of_modelCertificates F ψ ν π (σ 0) lambda (ell 0) μA
    (lt_trans (firstBlock_lt_total h) htr) hπ (hσ 0) hlambda hell hμA hcert.1 hcert.2.2

/-- The actual strictly dominant lower induction and both actual blocks have complete
symmetric L certificates with the required divisibility direction. -/
def StrictTwoBlockSymmetricLBound : Prop :=
  ∃ P P₁ P₂ : Polynomial ℂ,
    IsPadicSymmetricLPolynomial F ψ ν.val π (TwoBlockJacquet.inducedRep F h σ) P ∧
    IsPadicSymmetricLPolynomial F ψ ν.val π (σ 0) P₁ ∧
    IsPadicSymmetricLPolynomial F ψ ν.val π (σ 1) P₂ ∧
    ∃ (Q : Polynomial ℂ) (e : ℕ), X ^ e * (P₁ * P₂) = Q * P

set_option maxHeartbeats 1600000 in
/-- Identify the retained first-block polynomials in both directions and apply
the intrinsic bound to a certified whole-pair L polynomial. -/
theorem strictTwoBlockSymmetricLBound_of_rationalComparison
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσtype : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hlambda : lambda.val ≠ 0) (hell : ∀ i, (ell i).val ≠ 0)
    (hσ : ∀ i, IsSmooth (σ i))
    (J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
    (μN : Measure (LeftUnipotentQuotient t F.Carrier))
    (μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
    (μB : Measure (LeftUnipotentQuotient (m 1) F.Carrier))
    (hμN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μN)
    (hμA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) μA)
    (hμB : IsCompatible (upperUnipotent (m 1 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 1)) (unipotentHaar F.Carrier (m 1)) μB)
    (hR : StrictTwoBlockRationalComparison F h htr ψ ν π lambda σ ell hσ J μN μA μB) :
    StrictTwoBlockSymmetricLBound F h ψ ν π σ := by
  obtain ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D,
    hcert₁, hcert₂, -, -, hbound⟩ := hR
  have hfirst := StrictFirstBlockFactorCertificate.symmetricFactors F h htr ψ ν π lambda σ
    hπ hσtype hlambda ell (hell 0) hμA hcert₁
  have hπD := isOfWhittakerType_firstDual ψ π hπ
  have hσD := reversedDualBlocks_whittakerType F σ ψ hσtype
  have hsecond := StrictFirstBlockFactorCertificate.symmetricFactors F (reverse_sum h) htr
    (ψ.scale (-1)) (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
    (firstDualFunctional ψ π lambda)
    (fun i : Fin 2 => inverseTransposePullback (σ i.rev)) hπD hσD
    (firstDualFunctional_ne_zero ψ π hlambda)
    (fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev))
    (secondDualFunctional_ne_zero ψ (σ (0 : Fin 2).rev) (hell (0 : Fin 2).rev))
    hμB hcert₂
  have hP₂ : IsPadicSymmetricLPolynomial F ψ ν.val π (σ 1) P₂ := by
    have hh := hsecond.2.2.1
    change IsPadicSymmetricLPolynomial F ((ψ.scale (-1)).scale (-1)) ν.val
      (inverseTransposePullback (inverseTransposePullback π))
      (inverseTransposePullback (inverseTransposePullback (σ 1))) P₂ at hh
    simpa only [UnitaryAdditiveCharacter.scale_scale, neg_one_mul, neg_neg,
      UnitaryAdditiveCharacter.scale_one, inverseTransposePullback_involutive] using hh
  have hIndInv := lowerInduced_inverseWhittakerType F h ψ σ hσtype
  have hInd := (isOfWhittakerType_standard_iff_inverse ψ
    (TwoBlockJacquet.inducedRep F h σ)).mpr hIndInv
  obtain ⟨P, hP⟩ := symmetricLPolynomialExists p F ψ ν r t V
    (TwoBlockJacquet.Sections F h σ) π (TwoBlockJacquet.inducedRep F h σ) hπ hInd
  have hPμ := ((isPadicSymmetricLPolynomial_of_le htr.le).mp hP).2 μN hμN
  exact ⟨P, P₁, P₂, hP, hfirst.2.1, hP₂, hbound 0 (r - t - 1) (by omega) P
      (((isPairLPolynomial_of_lt htr).mp hPμ) 0 (r - t - 1) (by omega))⟩

omit lambda σ ell in
include htr in
set_option maxHeartbeats 1600000 in
/-- Complete symmetric L certificates satisfy the required bound for all
sufficiently large real opposite twists of arbitrary Whittaker-type blocks.
The independently owned first-block theorem remains an explicit premise. -/
theorem exists_strictTwoBlockSymmetricLBound
    (H : TwoBlockDominantFirstBlockLaurentIdentityStatement.{uF,uV,uW})
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)) :
    ∃ Cbound : ℝ, ∀ u : ℝ, Cbound < u →
      StrictTwoBlockSymmetricLBound F h ψ ν π (twoBlockOppositeTwistBlocks F m τ u) := by
  let := unipotentHaar_isMulRightInvariant F.Carrier t
  let := unipotentHaar_isMulRightInvariant F.Carrier (m 0)
  let := unipotentHaar_isMulRightInvariant F.Carrier (m 1)
  obtain ⟨lambda, hlambda⟩ := hπ.exists_ne_zero
  have hex : ∀ i, ∃ ell : glInverseFunctionals ψ (m i) (τ i), ell.val ≠ 0 :=
    fun i => ((isOfWhittakerType_standard_iff_inverse ψ (τ i)).mp (hτ i)).exists_ne_zero
  choose ell0 hell0 using hex
  obtain ⟨Cbound, hCbound⟩ := exists_strictTwoBlockRationalComparison F h htr ψ ν π lambda
    H hπ hlambda τ hτ ell0 hell0
  refine ⟨Cbound, fun u hu => ?_⟩
  obtain ⟨-, Ju, -, -, hR⟩ := hCbound u hu
  let σu := twoBlockOppositeTwistBlocks F m τ u
  have hσu : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σu i) :=
    fun i => (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).mpr
      (hτ i)
  let μN := unipotentQuotientHaar F.Carrier t
  let μA := unipotentQuotientHaar F.Carrier (m 0)
  let μB := unipotentQuotientHaar F.Carrier (m 1)
  have hμN := unipotentQuotientHaar_isCompatible F.Carrier t
  have hμA := unipotentQuotientHaar_isCompatible F.Carrier (m 0)
  have hμB := unipotentQuotientHaar_isCompatible F.Carrier (m 1)
  exact strictTwoBlockSymmetricLBound_of_rationalComparison F h htr ψ ν π lambda σu
    (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i))
    hπ hσu hlambda hell0 (fun i => (hσu i).1.1) Ju μN μA μB hμN hμA hμB
    (hR μN μA μB hμN hμA hμB)


end Langlands.RankinSelberg.DominantRankTransport
