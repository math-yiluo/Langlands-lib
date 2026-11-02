import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualRational
import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
import Langlands.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputProof
import Langlands.Representation.RankinSelberg.SymmetricGammaExpressionProof

/-! # Identify retained block witnesses with symmetric factors -/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  Polynomial TwoBlockLowerUnipotentQuotient

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance equalFactorsTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance equalFactorsValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance equalFactorsLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance equalFactorsT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance equalFactorsMeasurable : MeasurableSpace F.Carrier := borel _
local instance equalFactorsBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance equalFactorsGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance equalFactorsGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalFactorsUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance equalFactorsUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalFactorsQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance equalFactorsQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

section Identification

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {U : Type uW} [AddCommGroup U] [Module ℂ U]
  (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) U)
  (lambda : glFunctionals ψ r π) (ell : glInverseFunctionals ψ n σ)
  (μ : Measure (LeftUnipotentQuotient n F.Carrier))

set_option maxHeartbeats 800000 in
/-- A model generator at one complementary rectangle determines the full
symmetric L certificate, including every compatible quotient measure. -/
theorem symmetricLPolynomial_of_modelGenerator
    (hnr : n < r)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (hlambda : lambda.val ≠ 0) (hell : ell.val ≠ 0)
    (hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ)
    (j k : ℕ) (hr : r = n + (j + k + 1)) {P : Polynomial ℂ}
    (hP : IsNormalizedGenerator
      (unequalRankValuesAt j k hr qF ψ abv μ
        (rectangularMeasure ν.val j (n + 1)) π σ lambda ell) P) :
    IsPadicSymmetricLPolynomial F ψ ν.val π σ P := by
  have hσinv := (isOfWhittakerType_standard_iff_inverse ψ σ).mp hσ
  have hA : UnequalRankAnalyticAt j k hr qF ψ abv μ
      (rectangularMeasure ν.val j (n + 1)) π σ lambda ell := by
    subst r
    exact unequalRankAnalytic F F.canonicalTopologicalData n j k ψ μ hμ ν.val
      V U π σ hπ hσinv lambda ell hlambda hell
  obtain ⟨P₀, hP₀⟩ := symmetricLPolynomialExists p F ψ ν r n V U π σ hπ hσ
  have hP₀intrinsic := ((isPairLPolynomial_of_lt hnr).mp
    (((isPadicSymmetricLPolynomial_of_le hnr.le).mp hP₀).2 μ hμ)) j k hr
  have hEq : P = P₀ := hP.unique
    ((UnequalRankAnalyticAt.isNormalizedGenerator_iff j k hr hA
      hπ hσinv hlambda hell P₀).mp hP₀intrinsic)
  rw [hEq]
  exact hP₀

set_option maxHeartbeats 800000 in
/-- A fixed epsilon equation and its actual original and dual model generators
are the symmetric epsilon, L and gamma certificates for the same witnesses. -/
theorem symmetricFactors_of_modelCertificates
    (hnr : n < r)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (hlambda : lambda.val ≠ 0) (hell : ell.val ≠ 0)
    (hμ : IsCompatible (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ)
    {c : ℂˣ} {d : ℤ} {P Pdual : Polynomial ℂ}
    (hFE : UnequalRankEpsilonEquation hnr qF ψ abv μ ν.val π σ lambda ell c d)
    (hgen : ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      IsNormalizedGenerator
        (unequalRankValuesAt j k hr qF ψ abv μ
          (rectangularMeasure ν.val j (n + 1)) π σ lambda ell) P ∧
      IsNormalizedGenerator
        (dualUnequalRankRationalValuesAt hnr j k hr qF ψ abv μ ν.val
          π σ lambda ell) Pdual) :
    IsPadicSymmetricEpsilonFactor F ψ ν.val π σ (c, d) ∧
    IsPadicSymmetricLPolynomial F ψ ν.val π σ P ∧
    IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback π) (inverseTransposePullback σ) Pdual ∧
    IsPadicSymmetricGammaFactor F ψ ν.val π σ
      (rationalGammaExpression (LocalFactor.residueReflection F) c d P Pdual) := by
  have hr : r = n + (0 + (r - n - 1) + 1) := by omega
  have hP := symmetricLPolynomial_of_modelGenerator F ψ ν π σ lambda ell μ
    hnr hπ hσ hlambda hell hμ 0 (r - n - 1) hr (hgen _ _ hr).1
  have hσinv := (isOfWhittakerType_standard_iff_inverse ψ σ).mp hσ
  have hπD := isOfWhittakerType_firstDual ψ π hπ
  have hσDinv := isOfWhittakerType_secondDual ψ σ hσinv
  have hσD := (isOfWhittakerType_standard_iff_inverse (ψ.scale (-1))
    (inverseTransposePullback σ)).mpr hσDinv
  have hdual := (hgen 0 (r - n - 1) hr).2
  rw [dualUnequalRankRationalValuesAt_eq] at hdual
  have hPd := symmetricLPolynomial_of_modelGenerator F (ψ.scale (-1))
    (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
    (inverseTransposePullback σ) (firstDualFunctional ψ π lambda)
    (secondDualFunctional ψ σ ell) μ hnr hπD hσD
    (firstDualFunctional_ne_zero ψ π hlambda) (secondDualFunctional_ne_zero ψ σ hell)
    hμ (r - n - 1) 0 (by omega) hdual
  have he : IsPadicPairEpsilonFactor F ψ ν.val π σ (c, d) := by
    apply (isPairEpsilonFactor_of_lt hnr).mpr
    apply unequalRankEpsilonFactor_of_equation hnr hπ hσinv hlambda hell
    rwa [unipotentQuotientHaar_unique F.Carrier n μ hμ] at hFE
  have hG := IsPadicPairEpsilonFactor.gammaFactor_of_constructionInput F ψ ν.val π σ
    (padicPairGammaConstructionInput_of_whittakerType F ψ ν r n V U π σ hnr.le hπ hσinv)
    he ((isPadicSymmetricLPolynomial_of_le hnr.le).mp hP)
    ((isPadicSymmetricLPolynomial_of_le hnr.le).mp hPd)
  exact ⟨(isPadicSymmetricEpsilonFactor_of_le hnr.le).mpr he, hP, hPd,
    (isPadicSymmetricGammaFactor_of_le hnr.le).mpr hG⟩

end Identification

section Blocks

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local instance equalFactorsReverseAdd : ∀ i : Fin 2, AddCommGroup (W i.rev) :=
  fun i => hadd i.rev
local instance equalFactorsReverseModule : ∀ i : Fin 2, Module ℂ (W i.rev) :=
  fun i => hmod i.rev

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V)
  (lambda : glFunctionals ψ t π)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))

/-- The full symmetric certificates attached to the retained first-block
monomial and polynomial pair. -/
def EqualFirstBlockSymmetricFactors (c : ℂˣ) (d : ℤ)
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
theorem EqualFirstBlockFactorCertificate.symmetricFactors
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hlambda : lambda.val ≠ 0)
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (hell : (ell 0).val ≠ 0)
    {μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)}
    (hμA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) μA)
    {ζ c : ℂˣ} {d : ℤ} {P Pdual : Polynomial ℂ}
    (hcert : EqualFirstBlockFactorCertificate F h ψ ν π lambda σ ell μA
      ζ c d P Pdual) :
    EqualFirstBlockSymmetricFactors F ψ ν π σ c d P Pdual :=
  symmetricFactors_of_modelCertificates F ψ ν π (σ 0) lambda (ell 0) μA
    (firstBlock_lt_total h) hπ (hσ 0) hlambda hell hμA hcert.1 hcert.2.2

/-- The actual equal-rank lower induction and both actual blocks have complete
symmetric L certificates with the required divisibility direction. -/
def EqualTwoBlockSymmetricLBound : Prop :=
  ∃ P P₁ P₂ : Polynomial ℂ,
    IsPadicSymmetricLPolynomial F ψ ν.val π (TwoBlockJacquet.inducedRep F h σ) P ∧
    IsPadicSymmetricLPolynomial F ψ ν.val π (σ 0) P₁ ∧
    IsPadicSymmetricLPolynomial F ψ ν.val π (σ 1) P₂ ∧
    ∃ (Q : Polynomial ℂ) (e : ℕ), X ^ e * (P₁ * P₂) = Q * P

set_option maxHeartbeats 1600000 in
/-- Identify the retained first-block polynomials in both directions and apply
the intrinsic bound to a certified whole-pair L polynomial. -/
theorem equalTwoBlockSymmetricLBound_of_rationalComparison
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
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
    (hR : EqualTwoBlockRationalComparison F h ψ ν π lambda σ ell hσ J μN μA μB) :
    EqualTwoBlockSymmetricLBound F h ψ ν π σ := by
  obtain ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D,
    hcert₁, hcert₂, -, -, hbound⟩ := hR
  have hfirst := EqualFirstBlockFactorCertificate.symmetricFactors F h ψ ν π lambda σ
    hπ hσtype hlambda ell (hell 0) hμA hcert₁
  have hπD := isOfWhittakerType_firstDual ψ π hπ
  have hσD := reversedDualBlocks_whittakerType F σ ψ hσtype
  have hsecond := EqualFirstBlockFactorCertificate.symmetricFactors F (reverse_sum h)
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
  obtain ⟨P, hP⟩ := symmetricLPolynomialExists p F ψ ν t t V
    (TwoBlockJacquet.Sections F h σ) π (TwoBlockJacquet.inducedRep F h σ) hπ hInd
  have hPμ := ((isPadicSymmetricLPolynomial_of_le (le_refl t)).mp hP).2 μN hμN
  exact ⟨P, P₁, P₂, hP, hfirst.2.1, hP₂, hbound P (isPairLPolynomial_self.mp hPμ)⟩

omit lambda σ ell in
set_option maxHeartbeats 1600000 in
/-- Complete symmetric L certificates satisfy the required bound for all
sufficiently large real opposite twists of arbitrary Whittaker-type blocks.
No nonzero functional, measure compatibility or analytic identity is a premise. -/
theorem exists_equalTwoBlockSymmetricLBound
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)) :
    ∃ Cbound : ℝ, ∀ u : ℝ, Cbound < u →
      EqualTwoBlockSymmetricLBound F h ψ ν π (twoBlockOppositeTwistBlocks F m τ u) := by
  let := unipotentHaar_isMulRightInvariant F.Carrier t
  let := unipotentHaar_isMulRightInvariant F.Carrier (m 0)
  let := unipotentHaar_isMulRightInvariant F.Carrier (m 1)
  obtain ⟨lambda, hlambda⟩ := hπ.exists_ne_zero
  have hex : ∀ i, ∃ ell : glInverseFunctionals ψ (m i) (τ i), ell.val ≠ 0 :=
    fun i => ((isOfWhittakerType_standard_iff_inverse ψ (τ i)).mp (hτ i)).exists_ne_zero
  choose ell0 hell0 using hex
  obtain ⟨Cbound, hCbound⟩ := exists_equalTwoBlockRationalComparison F h ψ ν π lambda
    hπ hlambda τ hτ ell0 hell0
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
  exact equalTwoBlockSymmetricLBound_of_rationalComparison F h ψ ν π lambda σu
    (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i))
    hπ hσu hlambda hell0 (fun i => (hσu i).1.1) Ju μN μA μB hμN hμA hμB
    (hR μN μA μB hμN hμA hμB)

end Blocks

end Langlands.RankinSelberg.DominantRankTransport
