import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUpperParameters
import Langlands.Representation.RankinSelberg.UnequalRankBlockIntegrationProof
import Langlands.Representation.RankinSelberg.TwistInvariance

/-! Actual block coordinates for the complementary unipotent Fourier slice. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators

namespace Langlands.HarmonicAnalysis

open GeneralLinear RankinSelberg

universe uK

variable {K : Type uK}

/-- The scalar and the actual `m × 1` rectangular coordinate as one affine row. -/
def rankOneAffineParameters (m : ℕ) (z : K × Matrix (Fin m) (Fin 1) K) :
    Fin (m + 1) → K :=
  Fin.cons z.1 (fun i => z.2 i 0)

@[simp] theorem rankOneAffineParameters_zero (m : ℕ)
    (z : K × Matrix (Fin m) (Fin 1) K) : rankOneAffineParameters m z 0 = z.1 := rfl

@[simp] theorem rankOneAffineParameters_succ (m : ℕ)
    (z : K × Matrix (Fin m) (Fin 1) K) (i : Fin m) :
    rankOneAffineParameters m z i.succ = z.2 i 0 := rfl

variable [Field K]

/-- The first-column matrix on the complementary slice has determinant equal
  to its first affine coordinate, in every positive block rank. -/
theorem det_firstColumnMatrix (m : ℕ) (v : Fin (m + 1) → K) :
    Matrix.det (firstColumnMatrix (m + 1) v) = v 0 := by
  have hl : (firstColumnMatrix (m + 1) v).IsLowerTriangular := by
    intro i j hij
    have hj : j ≠ 0 := by intro h; subst j; exact (Fin.not_lt_zero i) hij
    have hne : i ≠ j := ne_of_lt hij
    simp only [firstColumnMatrix, ite_eq_right hj, ite_eq_right hne]
  rw [Matrix.det_of_isLowerTriangular _ hl, Fin.prod_univ_succ]
  have h0 : firstColumnMatrix (m + 1) v 0 0 = v 0 := by
    change Fin.lastCases 0 v (Fin.castSucc (0 : Fin (m + 1))) = v 0
    exact Fin.lastCases_castSucc _
  rw [h0]
  simp [firstColumnMatrix]

/-- The affine first-column matrix is the actual unequal-rank block matrix
  with `m` rectangular rows and final identity block of size one. -/
theorem firstColumnMatrix_eq_blockMatrixAt (m : ℕ)
    (g : Langlands.GeneralLinear (0 + 1) K) (X : Matrix (Fin m) (Fin (0 + 1)) K) :
    firstColumnMatrix (m + 1) (rankOneAffineParameters m (g 0 0, X)) =
      (AdjacentBlockReduction.blockMatrixAt m 0 (by omega) g X).val := by
  ext i j
  rw [AdjacentBlockReduction.blockMatrixAt_entry]
  by_cases hj : j = 0
  · subst j
    induction i using Fin.lastCases with
    | last =>
      have hbound : ¬ m + 1 < 1 + m := by omega
      simp [firstColumnMatrix, hbound]
    | cast i =>
      induction i using Fin.cases with
      | zero =>
        have hfirst : firstColumnMatrix (m + 1)
            (rankOneAffineParameters m (g 0 0, X)) (Fin.castSucc 0) 0 = g 0 0 := by
          change Fin.lastCases (0 : K) (rankOneAffineParameters m (g 0 0, X))
            (Fin.castSucc (0 : Fin (m + 1))) = g 0 0
          rw [Fin.lastCases_castSucc]
          rfl
        rw [hfirst]
        simp
      | succ i =>
        have hfirst : firstColumnMatrix (m + 1)
            (rankOneAffineParameters m (g 0 0, X)) i.succ.castSucc 0 = X i 0 := by
          change Fin.lastCases (0 : K) (rankOneAffineParameters m (g 0 0, X))
            i.succ.castSucc = X i 0
          rw [Fin.lastCases_castSucc]
          rfl
        rw [hfirst]
        have hbound : i.val + 1 < 1 + m := by omega
        simp [hbound]
  · have hjv : ¬j.val < 0 + 1 := by
      have := Fin.pos_of_ne_zero hj
      omega
    simp only [firstColumnMatrix, ite_eq_right hj, hjv, dite_false]
    by_cases hi : i.val < 0 + 1
    · have hie : i = 0 := by ext; simp only [Fin.val_zero]; omega
      subst i
      simp [Ne.symm hj]
    · simp [hi]

variable [MeasurableSpace K]

/-- Splitting the affine row into the scalar and the actual rectangular block. -/
def rankOneAffineParametersEquiv (m : ℕ) :
    (K × Matrix (Fin m) (Fin 1) K) ≃ᵐ (Fin (m + 1) → K) where
  toFun := rankOneAffineParameters m
  invFun v := (v 0, fun i _ => v i.succ)
  left_inv z := by
    refine Prod.ext ?_ ?_
    · rfl
    · funext i j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rfl
  right_inv v := by
    funext i
    induction i using Fin.cases <;> rfl
  measurable_toFun := by
    apply Measurable.of_eval
    intro i
    induction i using Fin.cases with
    | zero => exact measurable_fst
    | succ i => exact (measurable_pi_apply 0).comp ((measurable_pi_apply i).comp measurable_snd)
  measurable_invFun := by
    apply (measurable_pi_apply 0).prodMk
    apply Measurable.of_eval
    intro i
    exact Measurable.of_eval (fun _ => measurable_pi_apply i.succ)

variable [TopologicalSpace K]

/-- No scalar occurs when the auxiliary row is split into the additive scalar
  and the actual `m × 1` rectangular measure from the supplied Haar. -/
theorem rankOneAffineParameters_preserving (ν : AdditiveHaarMeasure K)
    [SigmaFinite ν.measure] (m : ℕ) :
    MeasurePreserving (rankOneAffineParametersEquiv (K := K) m)
      (ν.measure.prod (rectangularMeasure ν m 1)) (rowMeasure ν (m + 1)) := by
  have hr := measurePreserving_pi (fun _ : Fin m => rowMeasure ν 1)
    (fun _ : Fin m => ν.measure)
    (fun _ => measurePreserving_piUnique (fun _ : Fin 1 => ν.measure))
  have hp := (MeasurePreserving.id ν.measure).prod hr
  have hc := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 1) => ν.measure) 0).symm
  change MeasurePreserving (rankOneAffineParametersEquiv (K := K) m)
    (ν.measure.prod (Measure.pi (fun _ : Fin m => rowMeasure ν 1)))
    (Measure.pi (fun _ : Fin (m + 1) => ν.measure))
  convert! hc.comp hp using 1
  funext z i
  induction i using Fin.cases with
  | zero => simp [rankOneAffineParametersEquiv, rankOneAffineParameters,
      MeasurableEquiv.piFinSuccAbove]
  | succ i => simp [rankOneAffineParametersEquiv, rankOneAffineParameters,
      MeasurableEquiv.piFinSuccAbove]

end Langlands.HarmonicAnalysis
