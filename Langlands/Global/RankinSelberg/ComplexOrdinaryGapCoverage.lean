import Langlands.Global.RankinSelberg.ComplexGapTailTests
import Langlands.Global.RankinSelberg.ComplexGapUnitaryFiber
import Langlands.Global.RankinSelberg.ComplexOrdinaryAdjacentCoverage

/-! # Ordinary normalized coverage after adjoining a character -/

noncomputable section

open MeasureTheory MvPolynomial Set
open scoped Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.GeneralLinear
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.Analysis.SchwartzMatrixNorm (EntrySchwartz OperatorSchwartz operatorToEntry)
open Langlands.LocalFactor.Archimedean
open ComplexAdjacentUnfolding (whittakerVector whittakerVector_val)
open ComplexCompactProfileFamily (characterList)
open ComplexGapAlternateRestriction (GodementColumnFactors)
open ComplexGapExactRestriction (rotatedValue)
open ComplexGapLeadingCompact (exists_leadingSquareTest_one)
open ComplexGapMatchedTests (tailFactor)
open ComplexGapOrdinarySeparation (ordinaryWeylPhase)
open ComplexGapRankCoordinates (rankLT)
open ComplexGapRetained
open ComplexGapSeparatedKernels (retainedCoefficient)
open ComplexGapWeylRestriction (tailWeyl)
open ComplexGodement (addedCharacter retainedCharacters characterList_cons)
open ComplexGodementAddedCharacter (continuedValue)
open ComplexGodementContinuedModel (complexGodementContinuedModel)
open ComplexGodementGaussianPolynomial (Coordinates standardMatrixTest)
open ComplexJacquetContinuation (continuedJacquet complexJacquetIntertwiner complexJacquetNonzero)
open ComplexJacquetMultiplicityOne (complexJacquetMultiplicityOne exists_characterList)
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

variable (t q : ℕ)
local notation "Small" => t + 1
local notation "Rank" => t + 1 + q + 1
local notation "LowerIndex" => t + 1 + q
local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "KF[" es "]" => complexStandardKFinite Small es

private theorem rotatedStandard_mem (a : ℂˣ) (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (hds : ds.length = Rank)
    (hirr : IsIrreducibleGKModule (complexStandardRep (Rank + 1) (d :: ds))
      (complexStandardLie (Rank + 1) (d :: ds)))
    (W : complexWhittakerModel LowerIndex ds (-a)) (p : MvPolynomial (Coordinates Rank (Rank + 1)) ℂ) :
    rotatedValue t q a d (operatorToEntry (standardMatrixTest p)) W.val 0 ∈
      complexWhittakerModel (LowerIndex + 1) (d :: ds) (-a) := by
  obtain ⟨l, v, hList⟩ := exists_characterList (n := Rank + 1) (d :: ds) (by rw [List.length_cons, hds])
  have hc := List.cons.inj ((characterList_cons l v).symm.trans hList)
  let U : complexWhittakerModel LowerIndex (retainedCharacters l v) (-a) := ⟨W.val, hc.2.symm ▸ W.2⟩
  let ν := complexGeneralLinearHaar Rank
  let : ν.IsHaarMeasure := inferInstanceAs (complexGeneralLinearHaar Rank).IsHaarMeasure
  let : ν.IsMulRightInvariant := inferInstanceAs (complexGeneralLinearHaar Rank).IsMulRightInvariant
  have hW : (fun g => continuedValue ν (complexSelfDualMeasure a) d a (operatorToEntry (standardMatrixTest p)) W.val g 0) ∈
      complexWhittakerModel (LowerIndex + 1) (d :: ds) (-a) := by
    have hI : IsIrreducibleGKModule (complexStandardRep (Rank + 1) (characterList l v))
        (complexStandardLie (Rank + 1) (characterList l v)) := hList.symm ▸ hirr
    have h' := complexGodementContinuedModel ν (complexSelfDualMeasure a) a l v hI
      (standardMatrixTest p) (finiteDimensional_translateTest_standardMatrixTest p) U
    simpa only [hList, hc.1, U] using h'
  have hw : tailWeyl Small (q + 2) ∈ unitaryCompact ℂ (Rank + 1) := by
    unfold tailWeyl
    exact Langlands.Archimedean.ComplexBlockParabolicProof.blockDiagGL_mem_unitaryCompact'
      (Subgroup.one_mem _) (ComplexLocalDualWhittakerGauge.weylLong_mem_unitary (q + 2))
  exact rightTranslation_mem_complexWhittakerModel hW ⟨_, hw⟩

private def normalizationOfProduct {I L A : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hL : ∃ b : ℝ, ∀ s : ℂ, b < s.re → L s ≠ 0)
    (hRight : ∃ b : ℝ, ∀ s : ℂ, b < s.re → L s * I s = A s) :
    OrdinaryIntegralNormalization I (fun s => (L s)⁻¹) where
  value := A
  analytic := fun s _ => hA.analyticAt s
  eq_on_right := by
    obtain ⟨b, hb⟩ := hL
    obtain ⟨c, hc⟩ := hRight
    refine ⟨max b c, fun s hs => ?_⟩
    rw [← hc s ((le_max_right _ _).trans_lt hs), mul_comm (L s) (I s), mul_assoc,
      mul_inv_cancel₀ (hb s ((le_max_left _ _).trans_lt hs)), mul_one]

/-- At unit trace scale, pointwise ordinary normalized coverage for an unequal-rank pair
persists when a character is adjoined to the larger inducing list, provided the enlarged
and smaller standard modules are irreducible. -/
def ComplexOrdinaryGapCoverageStatement : Prop :=
  ∀ (a : ℂˣ), ‖(a : ℂ)‖ = 1 →
    ∀ (d : ComplexCharacterData) (ds es : List ComplexCharacterData), ds.length = Rank → es.length = Small →
    IsIrreducibleGKModule (complexStandardRep (Rank + 1) (d :: ds)) (complexStandardLie (Rank + 1) (d :: ds)) →
    IsIrreducibleGKModule (complexStandardRep Small es) (complexStandardLie Small es) →
    ∀ D : ComplexQuotientMeasureData t,
      HasCoveringOrdinaryNormalizations (complexOrdinaryUnequalTest (rankLT t q) ds es (-a) D)
        (complexPairLFactor ds es) →
      HasCoveringOrdinaryNormalizations (complexOrdinaryUnequalTest (rankLT t (q + 1)) (d :: ds) es (-a) D)
        (complexPairLFactor (d :: ds) es)

set_option maxHeartbeats 2200000 in
theorem complexOrdinaryGapCoverage : ComplexOrdinaryGapCoverageStatement t q := by
  intro a ha d ds es hds hes hirr hI D hCover s₀
  obtain ⟨l, v, rfl⟩ := exists_characterList es hes
  let e : Fin Small → ComplexCharacterData := fun i => characterOfParams (l i) (v i)
  let es := List.ofFn e
  let μ := complexSelfDualMeasure (-a)
  let B : KF[es] →ₗ[ℂ] (G Small → ℂ) := continuedJacquet μ (-a) l v
  have hB : IsComplexWhittakerIntertwiner t es a B := by
    simpa only [B, es, e, characterList, neg_neg] using complexJacquetIntertwiner t μ (-a) l v
  have hB₀ : B ≠ 0 := by
    obtain ⟨w, hw⟩ := complexJacquetNonzero t μ (-a) l v
    intro h
    exact hw (by change B w 1 = 0; rw [h]; rfl)
  have hRange : complexWhittakerModel t es a = B.range := by
    simpa only [B, es, e, characterList, neg_neg] using (complexJacquetMultiplicityOne t μ (-a) l v).2
  obtain ⟨⟨W, V⟩, N₀, hN₀⟩ := hCover s₀
  have hV : V.val ∈ complexWhittakerModel t es a := by
    simpa only [es, e, characterList, neg_neg] using V.2
  rw [hRange] at hV
  obtain ⟨v₀, hv₀⟩ := hV
  obtain ⟨A, hA, hChoose⟩ := complexGapRetainedNormalization t q a d ds hds e D W B hB
  let ev := (LinearMap.proj s₀).comp (A 1)
  have hev₀ : ev v₀ ≠ 0 := by
    have hRight : ∃ b : ℝ, ∀ s : ℂ, b < s.re →
        (complexPairLFactor ds es).denominator s * complexUnequalIntegral (rankLT t q) D W.val V.val s = A 1 v₀ s := by
      obtain ⟨b, hb⟩ := (hA v₀).2
      refine ⟨b, fun s hs => ?_⟩
      rw [← hv₀]
      exact (hb s hs).2.symm
    have hL := complexPairLFactor_denominator_ne_zero ds es
    let N := normalizationOfProduct (hA v₀).1 hL hRight
    obtain ⟨b, hb⟩ := hL
    have hEq := N.value_eq_of_factor_ne_zero N₀ ⟨b, fun s hs => inv_ne_zero (hb s hs)⟩
    change N.value s₀ ≠ 0
    rw [hEq]
    exact hN₀
  have hev : ev ≠ 0 := fun h => hev₀ (by rw [h]; rfl)
  obtain ⟨Ψ, P, f, F, hΨ, hTrace, hNonzero⟩ := exists_squareConvolution_trace_ne_zero
    (complexGeneralLinearHaar Small) d e hI a B hB hB₀ s₀ ev hev
  obtain ⟨p, hp⟩ := exists_leadingSquareTest_one t q P
  have hp' (X : Matrix (Fin Small) (Fin Small) ℂ) :
      ComplexGapSquareReflection.leadingSquareTest t q 1 (operatorToEntry (standardMatrixTest p)) X = Ψ X := by
    rw [hp, congrFun hΨ X]
  obtain ⟨Y, J, hCont, hEntire, hEnd⟩ := hChoose p f
  let C := retainedGroup t q
  let R (x : RetainedPoint t q) : ℂ := (d.character (determinant (C x)) : ℂ) * J x s₀
  have hR : Continuous R :=
    (((Units.continuous_val.comp d.character.continuous).comp determinantContinuous.continuous).comp
      (continuous_retainedGroup t q)).mul (hCont s₀)
  have hCenter (x : RetainedPoint t q) (hx : ∃ u : unitaryCompact ℂ Small, C x = rankInclusion (q + 1) u.val) :
      R x = ev (F s₀) := by
    obtain ⟨u, hu⟩ := hx
    have hAt := complexGapUnitaryFiber t q a d ds e D W B hB (A 1) hA
      (operatorToEntry (standardMatrixTest p)) Ψ hp' f F hTrace u (Y x) (J x) (hEntire x).1 (by
        obtain ⟨b, hb⟩ := hEnd x
        refine ⟨b, fun s hs => ?_⟩
        have h := hb s hs
        change retainedGroup t q x = _ at hu
        simpa only [hu] using And.intro h.1 h.2.1)
    change (d.character (determinant (C x)) : ℂ) * J x s₀ = A 1 (F s₀) s₀
    rw [hu]
    exact hAt s₀
  let V₁ := whittakerVector hB f
  obtain ⟨c, hc, hM⟩ := complexGapRetainedMellin t q a
  have hMellin (T : GodementColumnFactors Small q) (Φ : EntrySchwartz Rank (Rank + 1))
      (hLead : T.leading = operatorToEntry (standardMatrixTest p)) (hEval : ∀ X, Φ X = T.eval Small q X) :=
    hM D d ds es hds List.length_ofFn W V₁ T Φ hEval J hCont hEntire (fun x => by
      obtain ⟨b, hb⟩ := hEnd x
      refine ⟨b, fun s hs => ?_⟩
      simpa only [hLead, V₁, whittakerVector_val] using (hb s hs).2.2)
  have hInt (T : GodementColumnFactors Small q) (Φ : EntrySchwartz Rank (Rank + 1))
      (hLead : T.leading = operatorToEntry (standardMatrixTest p)) (hEval : ∀ X, Φ X = T.eval Small q X) :
      Integrable (fun x => tailFactor Small q a T (C x) * R x) (retainedHaar t q a) := by
    simpa only [C, R, retainedCoefficient, mul_assoc] using (hMellin T Φ hLead hEval).1 s₀
  have hHalf : Integrable (fun x => halfTailGaussian t q x * R x) (retainedHaar t q a) := by
    obtain ⟨T, Φ, hLead, hEval, hTail⟩ := exists_halfTailTest t q a (operatorToEntry (standardMatrixTest p))
    simpa only [C, hTail] using hInt T Φ hLead hEval
  have hPoly (Q : Fin (q + 2) → MvPolynomial (Fin Rank × Bool) ℂ) :
      Integrable (fun x => tailGaussianProduct t q Q (tailObservation t q x) * R x) (retainedHaar t q a) := by
    obtain ⟨T, Φ, hLead, hEval, hTail, _⟩ := complexGapTailTests t q a ha p Q
    simpa only [C, hTail] using hInt T (operatorToEntry Φ) hLead hEval
  let : (retainedHaar t q a).IsOpenPosMeasure := retainedHaar_isOpenPosMeasure t q a
  obtain ⟨Q, hQ⟩ := complexGapTailMoments t q (retainedHaar t q a) R hR (ev (F s₀)) hNonzero hCenter hHalf hPoly
  obtain ⟨T, Φ, hLead, hEval, hTail, p', rfl⟩ := complexGapTailTests t q a ha p Q
  let W₁ : complexWhittakerModel (LowerIndex + 1) (d :: ds) (-a) :=
    ⟨rotatedValue t q a d (operatorToEntry (standardMatrixTest p')) W.val 0, rotatedStandard_mem t q a d ds hds hirr W p'⟩
  let V₂ : complexWhittakerModel t es (-(-a)) := ⟨V₁.val, by simpa only [neg_neg] using V₁.2⟩
  let I (s : ℂ) := ∫ x, retainedCoefficient t q a d T (C x) * J x s ∂retainedHaar t q a
  have hI₀ : I s₀ ≠ 0 := by
    simpa only [I, C, retainedCoefficient, mul_assoc, hTail, R] using hQ
  let z := ordinaryWeylPhase t q d * (c : ℂ)
  have hz : z ≠ 0 := by
    unfold z ordinaryWeylPhase
    exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (by exact_mod_cast hc.ne')
  obtain ⟨_, hDiff, hRight⟩ := hMellin T (operatorToEntry (standardMatrixTest p')) hLead hEval
  have hNRight : ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      (complexPairLFactor (d :: ds) es).denominator s * complexUnequalIntegral (rankLT t (q + 1)) D W₁.val V₂.val s = z * I s := hRight
  let N := normalizationOfProduct (hDiff.const_mul z) (complexPairLFactor_denominator_ne_zero (d :: ds) es) hNRight
  exact ⟨(W₁, V₂), N, mul_ne_zero hz hI₀⟩

end Langlands.Global.RankinSelbergGlobal
