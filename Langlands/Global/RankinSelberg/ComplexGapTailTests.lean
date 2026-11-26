import Langlands.Global.RankinSelberg.ComplexGapTailMoments
import Langlands.Global.RankinSelberg.ComplexGapPartialFactors

/-! # Realizing the prescribed retained tail tests -/

noncomputable section

open MeasureTheory MvPolynomial Set
open scoped Matrix.Norms.Operator SchwartzMap NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapRetained

open ArchimedeanLocal Langlands.Archimedean Langlands.GeneralLinear
open Langlands.Analysis.SchwartzMatrixNorm (EntrySchwartz OperatorSchwartz operatorToEntry operatorToEntry_apply)
open Langlands.GodementJacquet (complexSelfDualMeasure_neg_scale complexAbsHom coe_complexAbsHom)
open Langlands.HarmonicAnalysis (rowMeasure)
open Langlands.LocalFactor.Archimedean (complexScaledCharacter_apply)
open ComplexGapAlternateRestriction (GodementColumnFactors)
open ComplexGapDualArguments (tailColumn)
open ComplexGapLeadingCompact (exists_standardMatrixTest_polynomialGaussian)
open ComplexGapLeadingHaar (retainedMeasure)
open ComplexGapMatchedTests (tailFactor)
open ComplexGapPartialFactors (columnProduct columnProduct_apply)
open ComplexGapRightChart (consecutiveTailWeight measurable_consecutiveTailWeight)
open ComplexGapSplitFourier (columnTransform columnTransform_apply fourier_columnTransform_neg)
open ComplexGapTailIwasawa (tailDiagonalMeasure tailModulus_pos measurable_tailModulus)
open ComplexGapTriangularChart (diagonalWeightMeasure)
open ComplexGapUnitDeterminant (normalizationWeight normalizationWeight_eq measurable_normalizationWeight)
open ComplexGodementColumnProduct (schwartzProd schwartzProd_apply)
open ComplexGodementGaussianPolynomial (Coordinates coordinates matrixSqNorm standardMatrixTest standardMatrixTest_apply standardColumnTest)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open ComplexLocalIwasawa (continuous_logTorus)
open ComplexLocalWhittakerGauge (logTorus)
open ComplexTraceFourier (realCoordinates standardGaussian transform transform_apply transform_standardGaussian)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel

variable (t q : ℕ)
local notation "Small" => t + 1
local notation "Rank" => t + 1 + q + 1
local notation "Ids" => Fin (q + 2)
local notation "Vec" => Fin Rank → ℂ
local notation "Idx" => Fin Rank × Bool
local notation "P" => RetainedPoint t q
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ
local notation "Col" => 𝓢(Vec, ℂ)
local notation "scale" => (2 * Real.pi : ℝ)

private theorem openPos_withDensity {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure] (f : X → ℝ≥0∞) (hf : Measurable f) (h : ∀ x, f x ≠ 0) :
    (μ.withDensity f).IsOpenPosMeasure :=
  (withDensity_absolutelyContinuous' hf.aemeasurable (ae_of_all _ h)).isOpenPosMeasure

/-- The retained measure is positive on every nonempty open set. -/
theorem retainedHaar_isOpenPosMeasure (a : ℂˣ) : (retainedHaar t q a).IsOpenPosMeasure := by
  let μ := complexSelfDualMeasure a
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : (tailDiagonalMeasure q).IsOpenPosMeasure := openPos_withDensity volume _ measurable_tailModulus
    (fun y => ENNReal.coe_ne_zero.mpr (tailModulus_pos y).ne')
  let : (diagonalWeightMeasure Small q).IsOpenPosMeasure :=
    openPos_withDensity (tailDiagonalMeasure q) _ ((measurable_consecutiveTailWeight Small q).comp continuous_logTorus.measurable)
      (fun y => by
        apply ENNReal.coe_ne_zero.mpr
        change ((complexAbsHom (logTorus y).val.det ^ Small)⁻¹ : ℝ≥0) ≠ 0
        apply inv_ne_zero (pow_ne_zero _ _)
        intro h
        have hz := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
        rw [coe_complexAbsHom, NNReal.coe_zero] at hz
        exact pow_ne_zero _ (norm_ne_zero_iff.mpr (logTorus y).det_ne_zero) hz)
  let δ := (diagonalWeightMeasure Small q).withDensity (fun y => (normalizationWeight Small q y : ℝ≥0∞))
  let : δ.IsOpenPosMeasure := openPos_withDensity (diagonalWeightMeasure Small q) _
    (measurable_normalizationWeight Small q) (fun y => by
      apply ENNReal.coe_ne_zero.mpr
      apply NNReal.coe_ne_zero.mp
      rw [normalizationWeight_eq Small q (Nat.succ_pos t)]
      exact Real.exp_ne_zero _)
  let : (entryHaar μ (q + 1)).IsHaarMeasure := upperEntryProductMeasure_isHaar μ
  let : SigmaFinite (entryHaar μ (q + 1)) := entryHaar_sigmaFinite μ _
  let : SigmaFinite δ := SigmaFinite.withDensity _
  change (((δ.prod (retainedCompactHaar t q)).prod (rowMeasure μ Small)).prod (entryHaar μ (q + 1))).IsOpenPosMeasure
  infer_instance

private theorem exists_standardColumn (Q : MvPolynomial Idx ℂ) :
    ∃ ψ : Col, ∀ x, ψ x = standardGaussian Q x := by
  let e (j : Idx) : Coordinates Rank 1 := (j.1, 0, j.2)
  obtain ⟨B, hB⟩ := exists_standardMatrixTest_polynomialGaussian (rename e Q)
  refine ⟨standardColumnTest B, fun x => ?_⟩
  let A : Mat Rank 1 := Matrix.of fun i _ => x i
  change standardMatrixTest B A = _
  rw [hB, standardGaussian, eval_rename]
  have hC : coordinates A ∘ e = realCoordinates x := by
    funext j
    rcases j with ⟨i,b⟩
    cases b <;> rfl
  have hN : matrixSqNorm A = ∑ i, ‖x i‖ ^ 2 := by
    simp only [matrixSqNorm, A, Matrix.of_apply, Fin.sum_univ_one]
  rw [hC, hN]

private theorem columnTransform_eq_negativeTransform (a : ℂˣ) (φ : Col) (x : Vec) :
    columnTransform a φ x = transform (-a) φ x := by
  rw [columnTransform_apply, transform_apply, complexSelfDualMeasure_neg_scale]
  unfold ComplexGodementFourier.fourier ComplexGodementFourier.piMeasure ComplexGodementFourier.psi
  apply integral_congr_ae (ae_of_all _ fun y => ?_)
  congr 1
  simp only [Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, complexScaledCharacter_apply,
    Units.val_neg, neg_mul, mul_neg, neg_neg]

private def prescribedTails (a : ℂˣ) (Φ : EntrySchwartz Rank Small) (ψ : Ids → Col) :
    GodementColumnFactors Small q where
  leading := Φ
  tail := Fin.lastCases (ψ 0) (fun j => columnTransform (-a) (ψ j.rev.succ))

private theorem prescribedTails_tailFactor (a : ℂˣ) (Φ : EntrySchwartz Rank Small) (ψ : Ids → Col) (p : P) :
    tailFactor Small q a (prescribedTails t q a Φ ψ) (retainedGroup t q p) =
      ∏ j, ψ j (tailObservation t q p j) := by
  rw [Fin.prod_univ_succ (fun j : Ids => ψ j (tailObservation t q p j))]
  unfold tailFactor prescribedTails tailObservation
  simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.rev_rev, Fin.cons_zero, Fin.cons_succ]
  apply congrArg (fun z : ℂ => ψ 0 (tailColumn Small q (retainedGroup t q p) 0) * z)
  refine Finset.prod_congr (s₁ := Finset.univ) rfl fun j _ => ?_
  simpa only [neg_neg] using fourier_columnTransform_neg (-a) (ψ j.succ)
    (tailColumn Small q (inverseTranspose Rank ℂ (retainedGroup t q p)) j)

section Entry

open scoped Matrix.Norms.Elementwise

private def leadingColumnsCLM : Mat Rank (Rank + 1) →L[ℝ] Mat Rank Small :=
  ({ toFun := fun X i j => X i (j.castAdd (q + 2))
     map_add' _ _ := rfl
     map_smul' _ _ := rfl } : Mat Rank (Rank + 1) →ₗ[ℝ] Mat Rank Small).toContinuousLinearMap

private def tailColumnsCLM : Mat Rank (Rank + 1) →L[ℝ] Mat Rank (q + 2) :=
  ({ toFun := fun X i j => X i (j.natAdd Small)
     map_add' _ _ := rfl
     map_smul' _ _ := rfl } : Mat Rank (Rank + 1) →ₗ[ℝ] Mat Rank (q + 2)).toContinuousLinearMap

private def splitEntryTest (T : GodementColumnFactors Small q) : EntrySchwartz Rank (Rank + 1) :=
  schwartzProd (leadingColumnsCLM t q) (tailColumnsCLM t q) zero_le_one (fun X => by
    rw [one_mul]
    refine (Matrix.norm_le_iff (by positivity)).mpr (fun i j => ?_)
    refine Fin.addCases (m := Small) («n» := q + 2) (fun j₀ => ?_) (fun j₁ => ?_) j
    · exact (Matrix.norm_entry_le_entrywise_sup_norm (leadingColumnsCLM t q X) (i := i) (j := j₀)).trans
        (le_add_of_nonneg_right (norm_nonneg _))
    · exact (Matrix.norm_entry_le_entrywise_sup_norm (tailColumnsCLM t q X) (i := i) (j := j₁)).trans
        (le_add_of_nonneg_left (norm_nonneg _))) T.leading (columnProduct Rank (q + 2) T.tail)

private theorem splitEntryTest_eval (T : GodementColumnFactors Small q) (X : Mat Rank (Rank + 1)) :
    splitEntryTest t q T X = T.eval Small q X := by
  rw [splitEntryTest, schwartzProd_apply, columnProduct_apply]
  rfl

end Entry

/-- The slower Gaussian can be prescribed independently of the leading rectangle. -/
theorem exists_halfTailTest (a : ℂˣ) (L : EntrySchwartz Rank Small) :
    ∃ (T : GodementColumnFactors Small q) (Φ : EntrySchwartz Rank (Rank + 1)),
      T.leading = L ∧ (∀ X, Φ X = T.eval Small q X) ∧
      ∀ p, tailFactor Small q a T (retainedGroup t q p) = halfTailGaussian t q p := by
  obtain ⟨ψ₀, hψ₀⟩ := exists_standardColumn t q 1
  let b := Real.sqrt (1 / 2 : ℝ)
  have hb : 0 < b := Real.sqrt_pos.mpr (by norm_num)
  let u := Units.mk0 (b : ℂ) (Complex.ofReal_ne_zero.mpr hb.ne')
  let ψ : Col := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := Vec) u).restrictScalars ℝ) ψ₀
  have hψ (x : Vec) : ψ x = (Real.exp (-scale * (∑ i, ‖x i‖ ^ 2) / 2) : ℂ) := by
    change ψ₀ ((b : ℂ) • x) = _
    rw [hψ₀, standardGaussian, map_one, one_mul]
    congr 2
    have he (i : Fin Rank) : ‖((b : ℂ) • x) i‖ ^ 2 = b ^ 2 * ‖x i‖ ^ 2 := by
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le, mul_pow]
    simp_rw [he]
    rw [← Finset.mul_sum, show b ^ 2 = (1 / 2 : ℝ) from Real.sq_sqrt (by norm_num)]
    ring
  let T := prescribedTails t q a L (fun _ => ψ)
  refine ⟨T, splitEntryTest t q T, rfl, splitEntryTest_eval t q T, fun p => ?_⟩
  rw [prescribedTails_tailFactor]
  simp_rw [hψ]
  rw [← Complex.ofReal_prod, ← Real.exp_sum, halfTailGaussian]
  congr 2
  rw [← Finset.sum_div, ← Finset.mul_sum]

/-- At unit trace scale, any product of standard polynomial Gaussian observations comes from
a standard rectangular polynomial Gaussian with the given leading rectangle. -/
def ComplexGapTailTestsStatement : Prop :=
  ∀ (a : ℂˣ), ‖(a : ℂ)‖ = 1 →
    ∀ (B : MvPolynomial (Coordinates Rank Small) ℂ) (Q : Ids → MvPolynomial Idx ℂ),
    ∃ (T : GodementColumnFactors Small q) (Φ : OperatorSchwartz Rank (Rank + 1)),
      T.leading = operatorToEntry (standardMatrixTest B) ∧
      (∀ X, operatorToEntry Φ X = T.eval Small q X) ∧
      (∀ p, tailFactor Small q a T (retainedGroup t q p) = tailGaussianProduct t q Q (tailObservation t q p)) ∧
      ∃ C : MvPolynomial (Coordinates Rank (Rank + 1)) ℂ, Φ = standardMatrixTest C

set_option maxHeartbeats 1500000 in
theorem complexGapTailTests : ComplexGapTailTestsStatement t q := by
  intro a ha B Q
  choose ψ hψ using fun j => exists_standardColumn t q (Q j)
  let T := prescribedTails t q a (operatorToEntry (standardMatrixTest B)) ψ
  have hT (j : Ids) : ∃ Q' : MvPolynomial Idx ℂ, ∀ x, T.tail j x = standardGaussian Q' x := by
    refine Fin.lastCases (motive := fun j => ∃ Q' : MvPolynomial Idx ℂ, ∀ x, T.tail j x = standardGaussian Q' x)
      ?_ (fun i => ?_) j
    · exact ⟨Q 0, fun x => by simpa only [T, prescribedTails, Fin.lastCases_last] using hψ 0 x⟩
    · obtain ⟨R, hR⟩ := transform_standardGaussian a ha (ψ i.rev.succ) (Q i.rev.succ) (hψ i.rev.succ)
      exact ⟨R, fun x => by simpa only [T, prescribedTails, Fin.lastCases_castSucc,
        columnTransform_eq_negativeTransform, neg_neg] using hR x⟩
  choose Q' hQ' using hT
  let e (j : Coordinates Rank Small) : Coordinates Rank (Rank + 1) := (j.1, j.2.1.castAdd (q + 2), j.2.2)
  let ej (i : Ids) (j : Idx) : Coordinates Rank (Rank + 1) := (j.1, i.natAdd Small, j.2)
  let C := rename e (ComplexGodementGaussianPolynomial.scalePolynomial B) * ∏ j, rename (ej j) (Q' j)
  obtain ⟨C', hC'⟩ := exists_standardMatrixTest_polynomialGaussian C
  refine ⟨T, standardMatrixTest C', rfl, fun X => ?_, fun p => ?_, C', rfl⟩
  · let Xe : Mat Rank Small := fun i j => X i (j.castAdd (q + 2))
    let Xj (j : Ids) : Vec := fun i => X i (j.natAdd Small)
    have he : coordinates X ∘ e = coordinates Xe := rfl
    have hej (j : Ids) : coordinates X ∘ ej j = realCoordinates (Xj j) := by
      funext i
      rcases i with ⟨i,b⟩
      cases b <;> rfl
    have hN : matrixSqNorm X = matrixSqNorm Xe + ∑ j, ∑ i, ‖Xj j i‖ ^ 2 := by
      have hf (i : Fin Rank) : (∑ j : Fin (Rank + 1), ‖X i j‖ ^ 2) =
          (∑ j : Fin Small, ‖Xe i j‖ ^ 2) + ∑ j : Ids, ‖Xj j i‖ ^ 2 := Fin.sum_univ_add (a := Small) (b := q + 2) (fun j => ‖X i j‖ ^ 2)
      simp only [matrixSqNorm, hf, Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_comm
    change standardMatrixTest C' X = standardMatrixTest B Xe * ∏ j, T.tail j (Xj j)
    rw [hC', standardMatrixTest_apply, hN, mul_add, Real.exp_add, Complex.ofReal_mul]
    simp only [C, map_mul, map_prod, eval_rename, he, hej, hQ', standardGaussian, Finset.prod_mul_distrib]
    have hExp : (∏ j, (Real.exp (-scale * ∑ i, ‖Xj j i‖ ^ 2) : ℂ)) =
        (Real.exp (-scale * ∑ j, ∑ i, ‖Xj j i‖ ^ 2) : ℂ) := by
      rw [← Complex.ofReal_prod, ← Real.exp_sum, Finset.mul_sum]
    rw [hExp]
    ring
  · rw [prescribedTails_tailFactor, tailGaussianProduct]
    exact Finset.prod_congr rfl (fun j _ => hψ j _)

end Langlands.Global.RankinSelbergGlobal.ComplexGapRetained
