import Langlands.Global.RankinSelberg.RealPairedSmoothRowAbsorption
import Langlands.Global.RankinSelberg.RealGapOrdinaryTailBound
import Langlands.Representation.Archimedean.SmoothScalarCoefficient

/-! # Toral decay of genuine smooth real Whittaker pairs -/

noncomputable section

open Matrix
open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 900000

namespace Langlands.Global.RankinSelbergGlobal.RealPairedWhittakerGauge

open CompletedProjectiveRepresentation RealPairedSmoothRowAbsorption
open RealPaddedWhittakerProduct (oppositeScale)
open RealLocalWhittaker (regularFunctions iteratedRightDerivative)
open RealWhittakerGauge (gauge_bound_of_derivative_growth_family)
open RealIwasawa (torus)
open RealConvergenceAnalysis (rootPos)
open RealGapOrdinaryTailBound (entrySup opNorm_le_entrySup)
open RealPlaceRestriction (realMatrixHeight_inv norm_entry_le_realMatrixHeight two_le_realMatrixHeight)

local notation "G" => fun n : ℕ => Langlands.GeneralLinear (n + 1) ℝ
local notation "A₀" => fun n : ℕ => Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
local notation "K" => fun n : ℕ => unitaryCompact ℝ (n + 1)
local notation "N" => fun n : ℕ => Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ
local notation "H" => Langlands.Archimedean.unitHeight

private theorem one_le_matrixHeight {r : ℕ} (g : G r) : 1 ≤ realMatrixHeight g :=
  (by norm_num : (1 : ℝ) ≤ 2).trans (two_le_realMatrixHeight (Nat.succ_pos r) g)

private theorem unitHeight_le_rank_matrixHeight {r : ℕ} (g : G r) :
    H g ≤ ((r + 1 : ℕ) : ℝ) * realMatrixHeight g := by
  have hRank : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos r
  have hNorm (x : G r) : ‖x.val‖ ≤ ((r + 1 : ℕ) : ℝ) * realMatrixHeight x := by
    have hPos : 0 ≤ realMatrixHeight x := zero_le_one.trans (one_le_matrixHeight x)
    have hEntry : entrySup x.val ≤ realMatrixHeight x :=
      (pi_norm_le_iff_of_nonneg hPos).mpr fun i => (pi_norm_le_iff_of_nonneg hPos).mpr fun j =>
        norm_entry_le_realMatrixHeight (Nat.succ_pos r) x i j
    exact (opNorm_le_entrySup x.val).trans (mul_le_mul_of_nonneg_left hEntry (zero_le_one.trans hRank))
  apply max_le (one_le_mul_of_one_le_of_one_le hRank (one_le_matrixHeight g))
  apply max_le (hNorm g)
  simpa only [realMatrixHeight_inv] using hNorm g⁻¹

variable (n : Fin 2 → ℕ)

local notation "A" => fun i => A₀ (n i)
local notation "B" => (∀ i : Fin 2, A i)
local notation "U" => Bˣ
local notation "I" => 𝓘(ℝ, B)
local notation "I₀" => fun i => matrixModel ℝ (n i + 1)

/-- Units acting in distinct factors commute. -/
theorem slot_commute {i j : Fin 2} (hij : i ≠ j) (g : G (n i)) (h : G (n j)) :
    Commute (slot n i g) (slot n j h) := by
  apply Units.ext
  funext k
  change (unitProjection A k (slot n i g * slot n j h)).val =
    (unitProjection A k (slot n j h * slot n i g)).val
  rw [map_mul, map_mul]
  by_cases hk : k = i
  · subst k
    simp [unitProjection_slot_of_ne, hij]
  · simp [unitProjection_slot_of_ne, hk]

/-- One-slot insertion preserves the exponential line. -/
theorem slot_exp (i : Fin 2) (X : A i) (t : ℝ) :
    slot n i (matrixExpUnit (n i + 1) (t • X)) =
      Langlands.LinearLieGroup.expUnit B (t • Pi.single i X) := by
  apply Units.ext
  funext j
  change (unitProjection A j (slot n i (matrixExpUnit (n i + 1) (t • X)))).val =
    NormedSpace.exp (t • Pi.single (M := A) i X) j
  have he := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (Pi.evalRingHom A j) (continuous_apply j)
    (x := t • Pi.single i X) (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)
  change NormedSpace.exp (t • Pi.single (M := A) i X) j =
    NormedSpace.exp (t • Pi.single (M := A) i X j) at he
  rw [he]
  by_cases h : j = i
  · subst j
    rw [unitProjection_slot_self, Pi.single_eq_same, matrixExpUnit_val]
  · rw [unitProjection_slot_of_ne n h, Pi.single_eq_of_ne h, smul_zero, NormedSpace.exp_zero]
    rfl

/-- A single-slot embedding is smooth for the product units chart. -/
theorem contMDiff_slot (i : Fin 2) : ContMDiff (I₀ i) I ∞ (slot n i) := by
  let L : A i →L[ℝ] B := ContinuousLinearMap.single ℝ A i
  have he (g : G (n i)) : (slot n i g).val = (1 : B) + L (g.val - 1) := by
    funext j
    change (unitProjection A j (slot n i g)).val = (1 : A j) + Pi.single (M := A) i (g.val - 1) j
    by_cases h : j = i
    · subst j
      simp only [unitProjection_slot_self, Pi.single_eq_same]
      abel
    · simp [unitProjection_slot_of_ne, h]
  have hc : ContMDiff (I₀ i) I ∞ (fun g : G (n i) => (slot n i g).val) := by
    simp_rw [he]
    exact contMDiff_const.add (L.contDiff.contMDiff.comp (Units.contMDiff_val.sub contMDiff_const))
  rw [contMDiff_iff_target]
  refine ⟨Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr hc.continuous, fun y => ?_⟩
  have h : extChartAt I y ∘ slot n i = fun g : G (n i) => (slot n i g).val := by
    funext g
    simp [extChartAt]
  rw [h]
  exact hc.contMDiffOn

private theorem slot_height (i : Fin 2) (g : G (n i)) : H (slot n i g) ≤ H g := by
  have h (u : G (n i)) : ‖(slot n i u).val‖ ≤ H u := by
    refine (pi_norm_le_iff_of_nonneg (zero_le_one.trans (Langlands.Archimedean.one_le_unitHeight u))).mpr fun j => ?_
    change ‖(unitProjection A j (slot n i u)).val‖ ≤ H u
    by_cases hj : j = i
    · subst j
      simpa only [unitProjection_slot_self] using Langlands.Archimedean.norm_val_le_unitHeight u
    · rw [unitProjection_slot_of_ne n hj, Units.val_one]
      exact norm_one.le.trans (Langlands.Archimedean.one_le_unitHeight u)
  refine max_le (Langlands.Archimedean.one_le_unitHeight g) (max_le (h g) ?_)
  rw [← map_inv]
  simpa only [Langlands.Archimedean.unitHeight_inv] using h g⁻¹

variable (E : Fin 2 → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)] (R : ∀ i, G (n i) →* (E i →L[ℂ] E i))

local notation "P" => productAction A R
local notation "D" => DerivativeSmoothVectors I P
local notation "act" => representation I P

/-- Evaluate the smooth product representation after acting in the two specified slots. -/
def coefficient (L : D →L[ℂ] ℂ) (i j : Fin 2) (h : G (n j)) (v : D) (g : G (n i)) : ℂ :=
  L (act (slot n j h * slot n i g) v)

omit [∀ i, CompleteSpace (E i)] in
private theorem contMDiff_coefficient (L : D →L[ℂ] ℂ) (i j : Fin 2) (h : G (n j)) (v : D) :
    ContMDiff (I₀ i) 𝓘(ℝ, ℂ) ∞ (coefficient n E R L i j h v) :=
  (contMDiff_smoothScalarCoefficient P L v).comp (contMDiff_const.mul (contMDiff_slot n i))

omit [∀ i, CompleteSpace (E i)] in
private theorem rightDerivative_coefficient (hR : IsContinuousRepresentation P)
    (L : D →L[ℂ] ℂ) (i j : Fin 2) (h : G (n j)) (v : D) (X : A i) :
    rightDerivative (I₀ i) X (coefficient n E R L i j h v) =
      coefficient n E R L i j h (operator I P (Pi.single i X) v) := by
  funext g
  have he (t : ℝ) : slot n j h * slot n i (g * matrixExpUnit (n i + 1) (t • X)) =
      (slot n j h * slot n i g) * Langlands.LinearLieGroup.expUnit B (t • Pi.single i X) := by
    rw [map_mul, mul_assoc, slot_exp]
  have h₁ := hasDerivAt_mul_matrixExpUnit_smul ((contMDiff_coefficient n E R L i j h v).of_le (by simp)) g X
  have h₂ := hasDerivAt_smoothScalarCoefficient_exp P hR L v (slot n j h * slot n i g) (Pi.single i X)
  simp only [coefficient, he] at h₁
  exact h₁.unique h₂

private def axisWord (i : Fin 2) : List (A i) → D → D
  | [] => id
  | X :: xs => fun v => operator I P (Pi.single i X) (axisWord i xs v)

omit [∀ i, CompleteSpace (E i)] in
private theorem iteratedRightDerivative_coefficient (hR : IsContinuousRepresentation P)
    (L : D →L[ℂ] ℂ) (i j : Fin 2) (h : G (n j)) (v : D) (Xs : List (A i)) :
    iteratedRightDerivative (n i) Xs (coefficient n E R L i j h v) =
      coefficient n E R L i j h (axisWord n E R i Xs v) := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change rightDerivative (I₀ i) X (iteratedRightDerivative (n i) Xs (coefficient n E R L i j h v)) = _
    rw [ih, rightDerivative_coefficient n E R hR]
    rfl

/-- A smooth Whittaker pair has simple-root decay along either factor uniformly after allowing
fixed polynomial growth in the other group. The two factors have the indicated opposite scales. -/
def RealPairedWhittakerGaugeStatement : Prop :=
  (∀ i, IsContinuousRepresentation (R i)) → ∀ (a : ℝˣ) (L : D →L[ℂ] ℂ),
    (∀ (i : Fin 2) (u : N (n i)) (v : D),
      L (act (slot n i u.val) v) = realWhittakerCharacter (oppositeScale a i) u.val * L v) →
    ∃ k : ℕ, ∀ (i j : Fin 2), i ≠ j → ∀ (v : D) (M : ℕ),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Fin (n i + 1) → ℝ) (b : K (n i)) (h : G (n j)),
        ‖coefficient n E R L i j h v (torus y * b.val)‖ ≤
          C * Real.exp (-(M : ℝ) * rootPos y + ((2 * k : ℕ) : ℝ) * ∑ j, |y j|) * realMatrixHeight h ^ k

set_option maxHeartbeats 1450000 in
theorem realPairedWhittakerGauge : RealPairedWhittakerGaugeStatement n E R := by
  intro hR a L hL
  let hP := isContinuous_productAction A R hR
  let p : Seminorm ℂ D := (normSeminorm ℂ ℂ).comp L.toLinearMap
  obtain ⟨C₀, d, hC₀, hNorm⟩ := exists_productNorm_bound n E R hR
  obtain ⟨k, q, _, hq⟩ := exists_seminorm_le_unitHeight_pow_of_norm_bound P hC₀ hNorm p L.continuous.norm
  refine ⟨k, fun i j hij v M => ?_⟩
  let bound (w : D) := ((n i + 1 : ℕ) : ℝ) ^ k * ((n j + 1 : ℕ) : ℝ) ^ k * q w
  let c (h : G (n j)) : ℂ := ((realMatrixHeight h ^ k : ℝ) : ℂ)⁻¹
  let W (h : G (n j)) (w : D) : G (n i) → ℂ :=
    fun g => c h * coefficient n E R L i j h w g
  have hW (h : G (n j)) (w : D) : W h w = coefficient n E R (c h • L) i j h w := rfl
  have hA (w : D) : 0 ≤ bound w := by dsimp [bound]; positivity
  have hBound (w : D) (h : G (n j)) (g : G (n i)) :
      ‖coefficient n E R L i j h w g‖ ≤ bound w * realMatrixHeight g ^ k * realMatrixHeight h ^ k := by
    let u := slot n j h * slot n i g
    have hu : H u ≤ ((n j + 1 : ℕ) : ℝ) * realMatrixHeight h *
        (((n i + 1 : ℕ) : ℝ) * realMatrixHeight g) := by
      refine (Langlands.Archimedean.unitHeight_mul_le _ _).trans ?_
      exact mul_le_mul ((slot_height n j h).trans (unitHeight_le_rank_matrixHeight h))
        ((slot_height n i g).trans (unitHeight_le_rank_matrixHeight g))
        (zero_le_one.trans (Langlands.Archimedean.one_le_unitHeight _))
        (mul_nonneg (by positivity) (zero_le_one.trans (one_le_matrixHeight h)))
    change ‖L (act u w)‖ ≤ _
    calc
      _ ≤ H u ^ k * q w := hq u w
      _ ≤ ((((n j + 1 : ℕ) : ℝ) * realMatrixHeight h) *
          (((n i + 1 : ℕ) : ℝ) * realMatrixHeight g)) ^ k * q w := by
        gcongr
        exact zero_le_one.trans (Langlands.Archimedean.one_le_unitHeight _)
      _ = _ := by simp only [bound, mul_pow]; ring
  have hWBound (w : D) (h : G (n j)) (g : G (n i)) : ‖W h w g‖ ≤ bound w * realMatrixHeight g ^ k := by
    have hPos : 0 < realMatrixHeight h ^ k := pow_pos (zero_lt_one.trans_le (one_le_matrixHeight h)) _
    simp only [W, norm_mul, c, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPos]
    calc
      _ ≤ (realMatrixHeight h ^ k)⁻¹ *
          (bound w * realMatrixHeight g ^ k * realMatrixHeight h ^ k) :=
        mul_le_mul_of_nonneg_left (hBound w h g) (inv_nonneg.mpr hPos.le)
      _ = _ := by field_simp
  have hReg (h : G (n j)) (w : D) : W h w ∈ regularFunctions (n i) (oppositeScale a i) := by
    refine ⟨?_, hW h w ▸ contMDiff_coefficient n E R (c h • L) i j h w,
      ⟨bound w, k, hA w, hWBound w h⟩⟩
    intro u hu g
    have hComm := (slot_commute n hij u h).eq
    have he : slot n j h * slot n i (u * g) = slot n i u * (slot n j h * slot n i g) := by
      rw [(slot n i).map_mul u g, ← mul_assoc, ← hComm, mul_assoc]
    change c h * L (act (slot n j h * slot n i (u * g)) w) =
      realWhittakerCharacter (oppositeScale a i) u * (c h * L (act (slot n j h * slot n i g) w))
    rw [he, map_mul, Module.End.mul_apply, hL i ⟨u, hu⟩]
    ring
  have hWord (h : G (n j)) (Xs : List (A i)) :
      iteratedRightDerivative (n i) Xs (W h v) = W h (axisWord n E R i Xs v) := by
    rw [hW h v, hW h _, iteratedRightDerivative_coefficient n E R hP]
  obtain ⟨C, hC, hGauge⟩ := gauge_bound_of_derivative_growth_family (fun h => W h v)
    (fun h Xs => hWord h Xs ▸ hReg h (axisWord n E R i Xs v))
    (fun Xs => ⟨bound (axisWord n E R i Xs v), hA _, fun h g => by rw [hWord]; exact hWBound _ _ _⟩) M
  refine ⟨C, hC, fun y b h => ?_⟩
  have hPos : 0 < realMatrixHeight h ^ k := pow_pos (zero_lt_one.trans_le (one_le_matrixHeight h)) _
  have hG := hGauge h y b
  simp only [rootPos, W, c, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPos] at hG ⊢
  exact (inv_mul_le_iff₀ hPos).mp hG |>.trans_eq (mul_comm _ _)

end Langlands.Global.RankinSelbergGlobal.RealPairedWhittakerGauge

namespace Langlands.Global.RankinSelbergGlobal.RealPairedWhittakerGauge

variable (n : Fin 2 → ℕ) (E : Fin 2 → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  (R : ∀ i, Langlands.GeneralLinear ((n i) + 1) ℝ →* (E i →L[ℂ] E i))

/-- The assertion for representations on complex Banach spaces. -/
def RealPairedWhittakerGaugeBanachStatement [∀ i, CompleteSpace (E i)] : Prop :=
  RealPairedWhittakerGaugeStatement n E R

theorem realPairedWhittakerGaugeBanach [∀ i, CompleteSpace (E i)] : RealPairedWhittakerGaugeBanachStatement n E R :=
  realPairedWhittakerGauge n E R

end Langlands.Global.RankinSelbergGlobal.RealPairedWhittakerGauge
