import Langlands.Global.RankinSelberg.RealGapOrdinaryTailBound
import Langlands.Global.RankinSelberg.RealWhittakerTranslateBound

/-! # The joint pointwise majorant for the ordinary real gap kernel -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapOrdinaryMajorant

open Langlands.Archimedean (unitaryCompact)
open ArchimedeanLocal (realNormalizedAbs)
open RealGapLeadingSchwartz (leadingStack realGapLeadingSchwartz matrixDecay weightedMatrixTail
  exists_integrable_weightedMatrixTail)
open RealGapOrdinaryTailBound (realGapOrdinaryTailBound entrySup entrySup_nonneg entrySup_le_opNorm
  opNorm_le_entrySup)
open RealIwasawa (alpha kpart npart npart_mul_torus_mul_kpart torus torus_val)
open RealPlaceRestriction (two_le_realMatrixHeight)
open RealTwoBlockHaar (rightTail tailColumns blockLog realTwoBlockIwasawa rightTail_norm_bounds
  realNormalizedAbs_det_rightTail)
open RealWhittakerTranslateBound (realWhittakerTranslateBound)
open RealWhittakerTranslatedMellin (HasGaugeBound)
open RealConvergenceAnalysis (rootPos)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "K" => fun n => unitaryCompact ℝ n
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℝ
local notation "H" => realMatrixHeight
local notation "δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))

local instance gapOrdinaryMajorantGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapOrdinaryMajorantGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩

/-- Stack the two leading blocks and reindex the rows into the ambient dimension. -/
def leadingInput {n k d : ℕ} (e : k + d = n) (A : Mat k k) (Y : Mat d k) : Mat n k :=
  e ▸ leadingStack A Y

theorem exists_leading_bound {n k d : ℕ} (e : k + d = n) (hn : 0 < n)
    (Φ : 𝓢(Mat n k, ℂ)) (p q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : G n) (A : Mat k k) (Y : Mat d k),
      ‖Φ (g.val * leadingInput e A Y)‖ ≤ C * H g ^ (p + q) * matrixDecay p A * matrixDecay q Y := by
  subst n
  obtain ⟨C, hC, h⟩ := realGapLeadingSchwartz k d hn Φ p q
  refine ⟨C, hC, fun g A Y => ?_⟩
  simpa only [leadingInput, matrixDecay, div_eq_mul_inv, mul_inv, mul_assoc] using h g A Y

private theorem normalizedDet_pos {n : ℕ} (g : G n) : 0 < δ g :=
  abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)

/-- The absolute determinant is the exponential of the sum of the logarithmic Iwasawa
coordinates. -/
theorem normalizedDet_eq_exp {n : ℕ} (g : G n) :
    δ g = Real.exp (∑ i, alpha g i) := by
  have he : (npart g).val * torus (alpha g) * (kpart g).val = g := npart_mul_torus_mul_kpart g
  have hu : (npart g).val.val.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (npart g).2.1, Finset.prod_eq_one fun i _ => (npart g).2.2 i]
  have hk : |(kpart g).val.val.det| = 1 :=
    Langlands.Archimedean.RealJacquetCoefficient.abs_det_eq_one_of_mem (kpart g).2
  change |g.val.det| = _
  conv_lhs => rw [← he]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hu, one_mul, abs_mul, hk,
    mul_one, torus_val, Matrix.det_diagonal, ← Real.exp_sum, abs_of_pos (Real.exp_pos _)]

private theorem normalizedDet_inv {n : ℕ} (g : G n) : δ g⁻¹ = (δ g)⁻¹ := by
  have hd : g⁻¹.val.det = g.val.det⁻¹ := by
    apply mul_left_cancel₀ g.det_ne_zero
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      mul_inv_cancel₀ g.det_ne_zero]
  simp only [realNormalizedAbs, hd, abs_inv]

private theorem normalizedDet_rpow_inv_le {n : ℕ} (g : G n) (β : ℝ) :
    δ g ^ β ≤ Real.exp (2 * |β| * ∑ i, |alpha g⁻¹ i|) := by
  have hd := normalizedDet_eq_exp g⁻¹
  rw [normalizedDet_inv, ← inv_inj, ← Real.exp_neg, inv_inv] at hd
  rw [hd, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  apply Real.exp_le_exp.mpr
  have h := Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i => alpha g⁻¹ i)
  have hs : 0 ≤ ∑ i, |alpha g⁻¹ i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc
    - (∑ i, alpha g⁻¹ i) * β ≤ |-(∑ i, alpha g⁻¹ i) * β| := le_abs_self _
    _ = |β| * |∑ i, alpha g⁻¹ i| := by rw [abs_mul, abs_neg]; ring
    _ ≤ |β| * ∑ i, |alpha g⁻¹ i| := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ ≤ _ := by nlinarith [abs_nonneg β]

private theorem sum_abs_blockLog {n k : ℕ} (hkn : k < n) (y : Fin k → ℝ) (z : Fin (n - k) → ℝ) :
    (∑ i, |blockLog hkn y z i|) = (∑ i, |y i|) + ∑ i, |z i| := by
  have h := Fintype.sum_equiv (finCongr (Nat.add_sub_of_le hkn.le)).symm
    (fun i => |blockLog hkn y z i|) (fun i => |Fin.append y z i|) (fun _ => rfl)
  rw [h, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

private theorem height_tail_mul_det_bound {r k : ℕ} (hk : 0 < k) (hkn : k < r + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : ℕ) (h : G (r + 1 - k)) (X : Mat k (r + 1 - k)) (v : K (r + 1)),
      let g := rightTail hk hkn h X v
      (H g * δ h ^ 2) ^ l ≤ C ^ l * (1 + ‖tailColumns hkn g‖) ^ (2 * (r + 1 + 1) * l) := by
  let n := r + 1
  let C := 2 * (n : ℝ) ^ 2 * (n.factorial : ℝ) ^ 2
  let m := 2 * (n + 1)
  refine ⟨C * ((n : ℝ) + 1) ^ m, by dsimp only [C]; positivity, fun l h X v => ?_⟩
  let g := rightTail hk hkn h X v
  have hB : H g * δ h ^ 2 ≤ C * (1 + ‖g.val‖) ^ m := by
    dsimp only
    rw [← realNormalizedAbs_det_rightTail hk hkn h X v]
    simpa only [C, n, m, realNormalizedAbs, Nat.cast_add, Nat.cast_one] using
      Langlands.GodementJacquet.realMatrixHeight_mul_absDet_sq_bound (r := r) g
  have hS : 1 + ‖g.val‖ ≤ ((n : ℝ) + 1) * (1 + ‖tailColumns hkn g‖) := by
    have h₀ : entrySup g.val ≤ 1 + entrySup (tailColumns hkn g) :=
      (rightTail_norm_bounds hk hkn h X v).2.2
    have h₁ := opNorm_le_entrySup g.val
    have h₂ := entrySup_le_opNorm (tailColumns hkn g)
    have hn : (1 : ℝ) ≤ n := by dsimp only [n]; exact_mod_cast Nat.succ_pos r
    have hT := norm_nonneg (tailColumns hkn g)
    have h₃ : (n : ℝ) * entrySup g.val ≤ n * (1 + ‖tailColumns hkn g‖) :=
      mul_le_mul_of_nonneg_left (h₀.trans (by linarith)) (zero_le_one.trans hn)
    nlinarith
  have hB' : H g * δ h ^ 2 ≤ (C * ((n : ℝ) + 1) ^ m) * (1 + ‖tailColumns hkn g‖) ^ m := by
    refine hB.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hS _) ?_).trans_eq ?_)
    · dsimp only [C]; positivity
    · rw [mul_pow]
      ring
  have hH : 0 ≤ H g := zero_le_two.trans (two_le_realMatrixHeight (Nat.succ_pos r) g)
  have hb := pow_le_pow_left₀ (mul_nonneg hH (pow_nonneg (normalizedDet_pos h).le 2)) hB' l
  simpa only [mul_pow, ← pow_mul (1 + ‖tailColumns hkn g‖), m, n] using hb

/-- Product of the split Schwartz factors, the two ordinary coefficients, and three
independent determinant weights. The tail measure density can be included in the tail power. -/
def ordinaryGapNorm {r t : ℕ} (h : t < r) (Φ : 𝓢(Mat (r + 1) (t + 1), ℂ))
    (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ)) (Ψ : 𝓢(Fin (r + 1) → ℝ, ℂ))
    (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ) (u s b : ℝ)
    (g z : G (t + 1)) (w : G (r + 1 - (t + 1))) (X : Mat (t + 1) (r + 1 - (t + 1)))
    (Y : Mat (r + 1 - (t + 1)) (t + 1)) (v : K (r + 1)) : ℝ :=
  let hkn := Nat.succ_lt_succ h
  let B := rightTail (Nat.succ_pos t) hkn w X v
  ‖Φ (B.val * leadingInput (Nat.add_sub_of_le hkn.le) z.val Y)‖ *
    ‖Ξ (tailColumns hkn B) * Ψ (B⁻¹.val (Fin.last r))‖ *
    ‖W (padGL hkn.le g * B⁻¹)‖ * ‖V (g * z)‖ * δ g ^ u * δ z ^ s * δ w ^ b

/-- The ordinary gap majorant separates the small quotient, the two square matrices,
and the two rectangular variables. The tail determinant power cancels its Haar density. -/
def RealGapOrdinaryMajorantStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ),
    HasGaugeBound W → HasGaugeBound V →
    ∀ (A : ℝ), 0 ≤ A → ∃ (σ τ : ℝ) (M : ℕ), ∀ (u s b : ℝ), σ ≤ u → τ ≤ s →
    ∀ (Φ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
      (Ψ : 𝓢(Fin (r + 1) → ℝ, ℂ)) (p q l : ℕ) (μ : Measure (G (t + 1))), μ.IsHaarMeasure →
      ∃ (C : ℝ) (j : ℕ), 0 ≤ C ∧ Integrable (weightedMatrixTail M j s) μ ∧
      ∀ (g z : G (t + 1)) (w : G (r + 1 - (t + 1))) (X : Mat (t + 1) (r + 1 - (t + 1)))
        (Y : Mat (r + 1 - (t + 1)) (t + 1)) (v : K (r + 1)),
      ordinaryGapNorm h Φ Ξ Ψ W V u s b g z w X Y v ≤
        C * Real.exp (-(A + 1) * ∑ i, |alpha g i|) * weightedMatrixTail M j s z *
          (δ w ^ (r + 1 - (t + 1)) * matrixDecay p w.val) * matrixDecay q X * matrixDecay l Y

set_option maxHeartbeats 1200000 in
theorem realGapOrdinaryMajorant : RealGapOrdinaryMajorantStatement := by
  intro r t h W V hWg hVg A hA
  let n := r + 1
  let k := t + 1
  let d := n - k
  let hk : 0 < k := Nat.succ_pos t
  let hkn : k < n := Nat.succ_lt_succ h
  obtain ⟨N, hW⟩ := hWg
  obtain ⟨N', hV⟩ := realWhittakerTranslateBound t V hVg
  obtain ⟨C₂, hC₂, hV₀⟩ := hV 0
  let M := N' * k
  let A₀ : ℝ := N + N' + A
  refine ⟨A₀ + 1, (k : ℝ) + 2 * M, M, fun u s b hu hs Φ Ξ Ψ p q l μ hμ => ?_⟩
  let : μ.IsHaarMeasure := hμ
  obtain ⟨j, hj⟩ := exists_integrable_weightedMatrixTail t M μ s hs
  obtain ⟨C₀, hC₀, hΦ⟩ := exists_leading_bound (Nat.add_sub_of_le hkn.le) (Nat.succ_pos r) Φ j l
  obtain ⟨C₃, hC₃, hH⟩ := height_tail_mul_det_bound hk hkn
  let β := b - 2 * (j + l : ℕ) - (d : ℝ)
  let B₀ : ℝ := N + 2 * |β|
  have hB₀ : 0 ≤ B₀ := by dsimp only [B₀]; positivity
  have hT : A₀ + 1 ≤ u := hu
  obtain ⟨J, C₄, hC₄, hTail⟩ := realGapOrdinaryTailBound r k hk hkn A₀ B₀ u hB₀ hT
    Ξ Ψ (2 * (n + 1) * (j + l)) p q
  obtain ⟨C₁, hC₁, hWJ⟩ := hW J
  refine ⟨C₀ * C₁ * C₂ * C₃ ^ (j + l) * C₄, j, by positivity, hj, fun g z w X Y v => ?_⟩
  let B := rightTail hk hkn w X v
  let y := alpha g
  let y' := alpha w⁻¹
  let x := blockLog hkn y y'
  let D := ‖Ξ (tailColumns hkn B) * Ψ (B⁻¹.val (Fin.last r))‖
  let S := 1 + ‖tailColumns hkn B‖
  let m := 2 * (n + 1) * (j + l)
  let Sy := ∑ i, |y i|
  let Sz := ∑ i, |y' i|
  let Sum := ∑ i, y i
  have hw := hWJ (padGL hkn.le g * B⁻¹)
  rw [realTwoBlockIwasawa n k hk hkn g w X v, sum_abs_blockLog] at hw
  have hv := hV₀ g z
  simp only [Nat.cast_zero, zero_mul, mul_zero, sub_zero, add_zero] at hv
  have hDg : δ g ^ u = Real.exp (u * Sum) := by
    rw [normalizedDet_eq_exp, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    dsimp only [Sum, y]
    ring
  have hD : 0 < δ w := normalizedDet_pos w
  have hHB : H B ^ (j + l) * δ w ^ b =
      (H B * δ w ^ 2) ^ (j + l) * δ w ^ (d : ℕ) * δ w ^ β := by
    rw [mul_pow, ← pow_mul]
    have he : δ w ^ (2 * (j + l) : ℕ) * δ w ^ d * δ w ^ β = δ w ^ b := by
      rw [← Real.rpow_natCast (δ w) (2 * (j + l)), ← Real.rpow_natCast (δ w) d, ← Real.rpow_add hD,
        ← Real.rpow_add hD]
      congr 1
      dsimp only [β]
      push_cast
      ring
    rw [← he]
    ring
  have hHB' : H B ^ (j + l) * δ w ^ b ≤ C₃ ^ (j + l) * S ^ m * δ w ^ d *
      Real.exp (2 * |β| * Sz) := by
    rw [hHB]
    refine mul_le_mul (mul_le_mul_of_nonneg_right (hH (j + l) w X v) (pow_nonneg hD.le _))
      (normalizedDet_rpow_inv_le w β) (Real.rpow_nonneg hD.le _) (by dsimp only [S, m]; positivity)
  have hF := hΦ B z.val Y
  have hE : Real.exp (-(J : ℝ) * rootPos x + (N : ℝ) * (Sy + Sz)) * Real.exp ((N' : ℝ) * Sy) *
      Real.exp (u * Sum) * Real.exp (2 * |β| * Sz) =
        Real.exp (-A * Sy) * Real.exp (A₀ * Sy + B₀ * Sz + u * Sum - (J : ℝ) * rootPos x) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [A₀, B₀]
    ring
  have hH' : 0 ≤ H z := zero_le_two.trans (two_le_realMatrixHeight hk z)
  have hY : 0 ≤ matrixDecay l Y := by unfold matrixDecay; positivity
  have hz : 0 ≤ matrixDecay j z.val := by unfold matrixDecay; positivity
  have hb : 0 ≤ δ z ^ s := Real.rpow_nonneg (normalizedDet_pos z).le _
  have hM : 0 ≤ weightedMatrixTail M j s z := by
    unfold weightedMatrixTail
    exact mul_nonneg (mul_nonneg (pow_nonneg hH' _) hb) hz
  have hMajor := hTail y w X v
  change D * S ^ m * _ ≤ C₄ * Real.exp (-Sy) * matrixDecay p w.val * matrixDecay q X at hMajor
  dsimp only [ordinaryGapNorm]
  change ‖Φ (B.val * leadingInput (Nat.add_sub_of_le hkn.le) z.val Y)‖ * D *
    ‖W (padGL hkn.le g * B⁻¹)‖ * ‖V (g * z)‖ * δ g ^ u * δ z ^ s * δ w ^ b ≤ _
  rw [hDg]
  calc
    _ ≤ (C₀ * H B ^ (j + l) * matrixDecay j z.val * matrixDecay l Y) * D *
        (C₁ * Real.exp (-(J : ℝ) * rootPos x + (N : ℝ) * (Sy + Sz))) *
        (C₂ * H z ^ M * Real.exp ((N' : ℝ) * Sy)) * Real.exp (u * Sum) * δ z ^ s * δ w ^ b := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hF (norm_nonneg _)) hw (norm_nonneg _) ?_)
          hv (norm_nonneg _) ?_) (Real.exp_nonneg _)) hb) (Real.rpow_nonneg hD.le _)
      · exact mul_nonneg ((norm_nonneg _).trans hF) (by dsimp only [D]; positivity)
      · exact mul_nonneg (mul_nonneg ((norm_nonneg _).trans hF) (by dsimp only [D]; positivity))
          (mul_nonneg hC₁ (Real.exp_nonneg _))
    _ = (C₀ * C₁ * C₂ * Real.exp (-(J : ℝ) * rootPos x + (N : ℝ) * (Sy + Sz)) *
          Real.exp ((N' : ℝ) * Sy) * Real.exp (u * Sum) * weightedMatrixTail M j s z *
          matrixDecay l Y * D) * (H B ^ (j + l) * δ w ^ b) := by unfold weightedMatrixTail; ring
    _ ≤ (C₀ * C₁ * C₂ * Real.exp (-(J : ℝ) * rootPos x + (N : ℝ) * (Sy + Sz)) *
          Real.exp ((N' : ℝ) * Sy) * Real.exp (u * Sum) * weightedMatrixTail M j s z *
          matrixDecay l Y * D) * (C₃ ^ (j + l) * S ^ m * δ w ^ d * Real.exp (2 * |β| * Sz)) :=
      mul_le_mul_of_nonneg_left hHB' (by dsimp only [D]; positivity)
    _ = (C₀ * C₁ * C₂ * C₃ ^ (j + l) * Real.exp (-A * Sy) * weightedMatrixTail M j s z *
        δ w ^ d * matrixDecay l Y) * (D * S ^ m *
          Real.exp (A₀ * Sy + B₀ * Sz + u * Sum - (J : ℝ) * rootPos x)) := by
      calc
        _ = (C₀ * C₁ * C₂ * C₃ ^ (j + l) * weightedMatrixTail M j s z * δ w ^ d * matrixDecay l Y *
              D * S ^ m) * (Real.exp (-(J : ℝ) * rootPos x + (N : ℝ) * (Sy + Sz)) *
              Real.exp ((N' : ℝ) * Sy) * Real.exp (u * Sum) * Real.exp (2 * |β| * Sz)) := by ring
        _ = _ := by rw [hE]; ring
    _ ≤ (C₀ * C₁ * C₂ * C₃ ^ (j + l) * Real.exp (-A * Sy) * weightedMatrixTail M j s z *
          δ w ^ d * matrixDecay l Y) * (C₄ * Real.exp (-Sy) * matrixDecay p w.val * matrixDecay q X) :=
      mul_le_mul_of_nonneg_left hMajor (by positivity)
    _ = _ := by
      rw [show -(A + 1) * Sy = -A * Sy + (-Sy) by ring, Real.exp_add]
      ring

end Langlands.Global.RankinSelbergGlobal.RealGapOrdinaryMajorant
