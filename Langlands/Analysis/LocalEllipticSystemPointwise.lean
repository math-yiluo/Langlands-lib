import Langlands.Analysis.LocalEllipticSystemBounds
import Langlands.Analysis.LocalSobolevPointwise

/-! # Interior pointwise derivative bounds for a finite elliptic system -/

noncomputable section

open scoped ContDiff ENNReal Nat
open MeasureTheory Metric Set

set_option autoImplicit false

namespace Langlands.Analysis

variable {d r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem derivWordNorm_le_opNorm_times_card (m : ℕ) (u : E → ℂ) (x : E) :
    derivWordNorm m u x ≤ (d : ℝ) ^ m * ‖iteratedFDeriv ℝ m u x‖ := by
  let T := iteratedFDeriv ℝ m u x
  let a (w : Fin m → Fin d) := ‖T (fun j => EuclideanSpace.basisFun (Fin d) ℝ (w j))‖
  change Real.sqrt (∑ w, a w ^ 2) ≤ _
  calc
    _ ≤ Real.sqrt ((∑ w, a w) ^ 2) := Real.sqrt_le_sqrt
      (Finset.sum_sq_le_sq_sum_of_nonneg (fun w _ => norm_nonneg _))
    _ = ∑ w, a w := Real.sqrt_sq (Finset.sum_nonneg fun w _ => norm_nonneg _)
    _ ≤ ∑ _w : Fin m → Fin d, ‖T‖ := by
      refine Finset.sum_le_sum fun w _ => T.unit_le_opNorm ?_
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => (norm_basisFun (w j)).le
    _ = _ := by simp [T]

private theorem weightedDerivative_le_of_pointwise {u : E → ℂ} {x₀ : E} {R : ℝ} (hR : 0 < R)
    (hu : ContDiffOn ℝ ∞ u (ball x₀ R))
    {m : ℕ} {B : ℝ} (hB : ∀ x ∈ ball x₀ R, ‖iteratedFDeriv ℝ m u x‖ ≤ B) :
    ballWeightedSeminorm (derivWordNorm m u) x₀ R m ≤
      (ENNReal.ofReal (R ^ m * (d : ℝ) ^ m) * volume (closedBall x₀ R) ^ (1 / 2 : ℝ)) *
        ENNReal.ofReal B := by
  unfold ballWeightedSeminorm
  refine iSup₂_le fun ρ hρ => ?_
  have hρ0 : 0 ≤ ρ := (half_pos hR).le.trans hρ.1
  have hρR : ball x₀ ρ ⊆ ball x₀ R := ball_subset_ball hρ.2.le
  have hmem : AEStronglyMeasurable (derivWordNorm m u) (volume.restrict (ball x₀ ρ)) :=
    ((continuousOn_derivWordNorm hu isOpen_ball m).mono hρR).aestronglyMeasurable measurableSet_ball
  have hlp := eLpNorm_le_of_ae_bound (p := 2) hmem
    ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (derivWordNorm_nonneg _ _ _)]
      exact (derivWordNorm_le_opNorm_times_card m u x).trans
        (mul_le_mul_of_nonneg_left (hB x (hρR hx)) (by positivity))))
  have hV : (volume (ball x₀ ρ) : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤
      volume (closedBall x₀ R) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow (measure_mono (hρR.trans ball_subset_closedBall)) (by norm_num)
  have hpow : (R - ρ) ^ m ≤ R ^ m :=
    pow_le_pow_left₀ (sub_nonneg.2 hρ.2.le) (sub_le_self R hρ0) m
  have hhalf : (2 : ℝ≥0∞).toReal⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [Measure.restrict_apply_univ, hhalf] at hlp
  calc
    _ ≤ ENNReal.ofReal (R ^ m) *
        (volume (closedBall x₀ R) ^ (1 / 2 : ℝ) * ENNReal.ofReal ((d : ℝ) ^ m * B)) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) (hlp.trans (mul_le_mul' hV le_rfl))
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      ac_rfl

private theorem eLpNorm_half_ball_le_weightedDerivative {u : E → ℂ} {x₀ : E} {R : ℝ} (hR : 0 < R)
    (hu : ContDiffOn ℝ ∞ u (ball x₀ R)) (m : ℕ) :
    eLpNorm (iteratedFDeriv ℝ m u) 2 (volume.restrict (ball x₀ (R / 2))) ≤
      (ENNReal.ofReal ((R - R / 2) ^ m))⁻¹ * ballWeightedSeminorm (derivWordNorm m u) x₀ R m := by
  have hρR : R / 2 < R := half_lt_self hR
  let F := ENNReal.ofReal ((R - R / 2) ^ m)
  have hF0 : F ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos (sub_pos.2 hρR) m)).ne'
  have hFt : F ≠ ⊤ := ENNReal.ofReal_ne_top
  have hn : eLpNorm (iteratedFDeriv ℝ m u) 2 (volume.restrict (ball x₀ (R / 2))) ≤
      eLpNorm (derivWordNorm m u) 2 (volume.restrict (ball x₀ (R / 2))) :=
    eLpNorm_mono_real
      ((continuousOn_iteratedFDeriv_ball (hu.mono (ball_subset_ball hρR.le)) m).aestronglyMeasurable
        measurableSet_ball)
      (fun x => norm_iteratedFDeriv_le_derivWordNorm m u x)
  refine hn.trans ?_
  have hW := le_ballWeightedSeminorm (G := derivWordNorm m u) (x₀ := x₀) m
    (show R / 2 ∈ Ico (R / 2) R from
    ⟨le_rfl, hρR⟩)
  have h := mul_le_mul' (le_refl F⁻¹) hW
  rwa [← mul_assoc, ENNReal.inv_mul_cancel hF0 hFt, one_mul] at h

/-- For a fixed local elliptic system with a common scalar operator of order
`r`, the norm of each derivative at the center is bounded linearly by a
common pointwise bound of the derivatives of orders less than `r`. -/
theorem exists_localEllipticSystem_derivative_bounds {ι : Type*} [Fintype ι] (hr : 0 < r)
    (D : CoordinateScalarOperator E d r) (hD : D.basis = (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
    (A : ι → ι → ℂ) {S : Set E} (hS : IsOpen S)
    (hcoef : ∀ (k : Fin (r + 1)) (w : Fin k.val → Fin d), ContDiffOn ℝ ∞ (D.coefficient k w) S)
    (hell : D.IsEllipticOn S) {x₀ : E} (hx₀ : x₀ ∈ S) :
    ∃ R : ℝ, 0 < R ∧ closedBall x₀ R ⊆ S ∧
      ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
        ∀ (u : ι → E → ℂ), (∀ i, ContDiffOn ℝ ∞ (u i) S) →
          (∀ i x, x ∈ S → D.action (u i) x = ∑ j, A i j * u j x) →
          ∀ B : ℝ,
            (∀ i m, m < r → ∀ x ∈ ball x₀ R, ‖iteratedFDeriv ℝ m (u i) x‖ ≤ B) →
              ∀ i m, ‖iteratedFDeriv ℝ m (u i) x₀‖ ≤ C m * max 0 B := by
  obtain ⟨R, hR, hsub, C, hC, hbound⟩ :=
    exists_localEllipticSystem_weighted_bounds hr D hD A hS hcoef hell hx₀
  let V := volume (closedBall x₀ R) ^ (1 / 2 : ℝ)
  have hV : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_closedBall_lt_top.ne
  let K := ∑ m ∈ Finset.range r, ENNReal.ofReal (R ^ m * (d : ℝ) ^ m) * V
  have hK : K ≠ ⊤ := ENNReal.sum_ne_top.2 fun m _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV
  let ρ := R / 2
  have hρ : 0 < ρ := half_pos hR
  have hρsub : ball x₀ ρ ⊆ ball x₀ R := ball_subset_ball (half_lt_self hR).le
  let L := fun m : ℕ => (ENNReal.ofReal ((R - ρ) ^ m))⁻¹ * C m * K
  have hL (m : ℕ) : L m ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (pow_pos (sub_pos.2 (half_lt_self hR)) m)).ne')
      (hC m)) hK
  let W := volume (ball x₀ ρ) ^ (1 / 2 : ℝ)
  have hWt : W ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne
  have hW0 : W ≠ 0 := (ENNReal.rpow_pos (measure_ball_pos volume x₀ hρ) measure_ball_lt_top.ne).ne'
  let n := Module.finrank ℝ E
  let P := fun m : ℕ => W⁻¹ * ((∑ j ∈ Finset.range (n + 1), ENNReal.ofReal (ρ ^ j / j !) *
    L (j + m)) + ENNReal.ofReal (ρ ^ (n + 1) / n !) * L (n + 1 + m))
  have hP (m : ℕ) : P m ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hW0)
    (ENNReal.add_ne_top.2
      ⟨ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hL _),
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hL _)⟩)
  refine ⟨R, hR, hsub, fun m => (P m).toReal, fun _ => ENNReal.toReal_nonneg, ?_⟩
  intro u hu heq B hB i m
  let M := ENNReal.ofReal B
  have hball : ball x₀ R ⊆ S := ball_subset_closedBall.trans hsub
  have hsm j := (hu j).mono hball
  have hinit (j : ι) (p : ℕ) (hp : p < r) :
      ballWeightedSeminorm (derivWordNorm p (u j)) x₀ R p ≤ K * M := by
    refine (weightedDerivative_le_of_pointwise hR (hsm j) (hB j p hp)).trans ?_
    exact mul_le_mul' (Finset.single_le_sum
      (f := fun p => ENNReal.ofReal (R ^ p * (d : ℝ) ^ p) * V)
      (fun _ _ => zero_le) (Finset.mem_range.2 hp)) le_rfl
  have hLp (p : ℕ) : eLpNorm (iteratedFDeriv ℝ p (u i)) 2 (volume.restrict (ball x₀ ρ))
      ≤ L p * M := by
    refine (eLpNorm_half_ball_le_weightedDerivative hR (hsm i) p).trans ?_
    dsimp only [L]
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul' le_rfl (hbound u hu heq (K * M) hinit i p)
  have hSob := measure_ball_rpow_mul_enorm_iteratedFDeriv_le volume hρ
    ((hsm i).mono hρsub) (le_refl n) m
  have hEval : W * ‖iteratedFDeriv ℝ m (u i) x₀‖ₑ ≤
      ((∑ j ∈ Finset.range (n + 1), ENNReal.ofReal (ρ ^ j / j !) * L (j + m)) +
        ENNReal.ofReal (ρ ^ (n + 1) / n !) * L (n + 1 + m)) * M := by
    refine hSob.trans ?_
    simp only [add_mul, Finset.sum_mul, mul_assoc]
    refine add_le_add (Finset.sum_le_sum fun j _ => mul_le_mul' le_rfl (hLp _))
      (mul_le_mul' le_rfl (hLp _))
  have hscaled := mul_le_mul' (le_refl W⁻¹) hEval
  rw [← mul_assoc W⁻¹ W, ENNReal.inv_mul_cancel hW0 hWt, one_mul, ← mul_assoc] at hscaled
  have hx := ENNReal.toReal_mono (ENNReal.mul_ne_top (hP m) ENNReal.ofReal_ne_top) hscaled
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal', toReal_enorm, max_comm B 0] at hx
  exact hx

end Langlands.Analysis
