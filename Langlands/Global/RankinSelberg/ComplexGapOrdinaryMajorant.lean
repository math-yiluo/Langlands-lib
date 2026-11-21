import Langlands.Global.RankinSelberg.ComplexGapOrdinaryTailBound
import Langlands.Global.RankinSelberg.ComplexWhittakerTranslateBound

/-! # The joint pointwise majorant for the ordinary complex gap kernel -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapOrdinaryMajorant

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ArchimedeanLocal (complexNormalizedAbs)
open ComplexGapLeadingSchwartz (leadingStack complexGapLeadingSchwartz matrixDecay weightedMatrixTail
  exists_integrable_weightedMatrixTail)
open ComplexGapOrdinaryTailBound (complexGapOrdinaryTailBound)
open ComplexLocalIwasawa (alpha kpart npart npart_mul_logTorus_mul_kpart)
open ComplexLocalOrdinaryConvergence (norm_detPower_logTorus_mul)
open ComplexLocalWhittakerGauge (logTorus)
open ComplexPlaceAnalytic (two_le_complexMatrixHeight)
open ComplexTwoBlockHaar (rightTail tailColumns blockLog complexTwoBlockIwasawa rightTail_norm_bounds
  complexNormalizedAbs_det_rightTail)
open ComplexWhittakerTranslateBound (complexWhittakerTranslateBound)
open ComplexWhittakerTranslatedMellin (compact_rightTranslate_uniformSimpleRootBound)
open RealConvergenceAnalysis (rootPos norm_cexp_mul_ofReal)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "K" => fun n => unitaryCompact ℂ n
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ
local notation "H" => complexMatrixHeight
local notation "δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))

/-- Stack the two leading blocks and reindex the rows into the ambient dimension. -/
def leadingInput {n k d : ℕ} (e : k + d = n) (A : Mat k k) (Y : Mat d k) : Mat n k :=
  e ▸ leadingStack A Y

theorem exists_leading_bound {n k d : ℕ} (e : k + d = n) (hn : 0 < n)
    (Φ : 𝓢(Mat n k, ℂ)) (p q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : G n) (A : Mat k k) (Y : Mat d k),
      ‖Φ (g.val * leadingInput e A Y)‖ ≤ C * H g ^ (p + q) * matrixDecay p A * matrixDecay q Y := by
  subst n
  obtain ⟨C, hC, h⟩ := complexGapLeadingSchwartz k d hn Φ p q
  refine ⟨C, hC, fun g A Y => ?_⟩
  simpa only [leadingInput, matrixDecay, div_eq_mul_inv, mul_inv, mul_assoc] using h g A Y

private theorem normalizedDet_pos {n : ℕ} (g : G n) : 0 < δ g :=
  pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)) _

/-- The normalized determinant modulus is the exponential of twice the sum of logarithmic
Iwasawa coordinates. -/
theorem normalizedDet_eq_exp {n : ℕ} (g : G n) :
    δ g = Real.exp (2 * ∑ i, alpha g i) := by
  let b := logTorus (alpha g) * (kpart g).val
  have he : (npart g).val * b = g := by rw [← mul_assoc, npart_mul_logTorus_mul_kpart]
  have hdet : g.val.det = b.val.det := by
    rw [← he, Units.val_mul, Matrix.det_mul, Langlands.RankinSelberg.unipotent_det, one_mul]
  have hnorm := norm_detPower_logTorus_mul (alpha g) (kpart g) 1
  change ‖ArchimedeanLocal.detPower complexNormalizedAbs b 1‖ = _ at hnorm
  rw [ArchimedeanLocal.detPower, norm_cexp_mul_ofReal, Complex.one_re, one_mul,
    Real.exp_log (normalizedDet_pos b)] at hnorm
  simpa only [hdet, mul_one] using hnorm

private theorem normalizedDet_inv {n : ℕ} (g : G n) : δ g⁻¹ = (δ g)⁻¹ := by
  have hd : g⁻¹.val.det = g.val.det⁻¹ := by
    apply mul_left_cancel₀ g.det_ne_zero
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      mul_inv_cancel₀ g.det_ne_zero]
  simp only [complexNormalizedAbs, hd, norm_inv, inv_pow]

private theorem normalizedDet_rpow_inv_le {n : ℕ} (g : G n) (β : ℝ) :
    δ g ^ β ≤ Real.exp (2 * |β| * ∑ i, |alpha g⁻¹ i|) := by
  have hd := normalizedDet_eq_exp g⁻¹
  rw [normalizedDet_inv, ← inv_inj, ← Real.exp_neg, inv_inv] at hd
  rw [hd, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  apply Real.exp_le_exp.mpr
  have h := Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i => alpha g⁻¹ i)
  calc
    - (2 * ∑ i, alpha g⁻¹ i) * β ≤ |-(2 * ∑ i, alpha g⁻¹ i) * β| := le_abs_self _
    _ = 2 * |β| * |∑ i, alpha g⁻¹ i| := by rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

private theorem sum_abs_blockLog {n k : ℕ} (hkn : k < n) (y : Fin k → ℝ) (z : Fin (n - k) → ℝ) :
    (∑ i, |blockLog hkn y z i|) = (∑ i, |y i|) + ∑ i, |z i| := by
  have h := Fintype.sum_equiv (finCongr (Nat.add_sub_of_le hkn.le)).symm
    (fun i => |blockLog hkn y z i|) (fun i => |Fin.append y z i|) (fun _ => rfl)
  rw [h, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

private theorem height_tail_mul_det_bound {r k : ℕ} (hk : 0 < k) (hkn : k < r + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : ℕ) (h : G (r + 1 - k)) (X : Mat k (r + 1 - k)) (v : K (r + 1)),
      let g := rightTail hk hkn h X v
      (H g * δ h) ^ l ≤ C ^ l * (1 + ‖tailColumns hkn g‖) ^ (2 * (r + 1 + 1) * l) := by
  let n := r + 1
  let C := 2 * (n : ℝ) ^ 2 * (n.factorial : ℝ) ^ 2
  let m := 2 * (n + 1)
  refine ⟨C * (2 : ℝ) ^ m, by dsimp only [C]; positivity, fun l h X v => ?_⟩
  let g := rightTail hk hkn h X v
  have hB : H g * δ h ≤ C * (1 + ‖g.val‖) ^ m := by
    dsimp only
    rw [← complexNormalizedAbs_det_rightTail hk hkn h X v]
    simpa only [C, n, m, Nat.cast_add, Nat.cast_one] using
      Langlands.GodementJacquet.complexMatrixHeight_mul_det_bound g
  have hS : 1 + ‖g.val‖ ≤ 2 * (1 + ‖tailColumns hkn g‖) := by
    have h := (rightTail_norm_bounds hk hkn h X v).2.2
    linarith [norm_nonneg (tailColumns hkn g)]
  have hB' : H g * δ h ≤ (C * (2 : ℝ) ^ m) * (1 + ‖tailColumns hkn g‖) ^ m := by
    refine hB.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hS _) ?_).trans_eq ?_)
    · dsimp only [C]; positivity
    · rw [mul_pow]
      dsimp only [C]
      ac_rfl
  have hH : 0 ≤ H g := zero_le_two.trans (two_le_complexMatrixHeight (Nat.succ_pos r) g)
  have hb := pow_le_pow_left₀ (mul_nonneg hH (normalizedDet_pos h).le) hB' l
  simpa only [mul_pow, ← pow_mul (1 + ‖tailColumns hkn g‖), m, n] using hb

/-- Product of the split Schwartz factors, the two ordinary coefficients, and three
independent determinant weights. The tail measure density can be included in the tail power. -/
def ordinaryGapNorm {r t : ℕ} (h : t < r) (Φ : 𝓢(Mat (r + 1) (t + 1), ℂ))
    (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ)) (Ψ : 𝓢(Fin (r + 1) → ℂ, ℂ))
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
def ComplexGapOrdinaryMajorantStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ds es : List ComplexCharacterData) (a : ℂˣ)
    (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a))
    (A : ℝ), 0 ≤ A → ∃ (σ τ : ℝ) (M : ℕ), ∀ (u s b : ℝ), σ ≤ u → τ ≤ s →
    ∀ (Φ : 𝓢(Mat (r + 1) (t + 1), ℂ)) (Ξ : 𝓢(Mat (r + 1) (r + 1 - (t + 1)), ℂ))
      (Ψ : 𝓢(Fin (r + 1) → ℂ, ℂ)) (p q l : ℕ),
      ∃ (C : ℝ) (j : ℕ), 0 ≤ C ∧ Integrable (weightedMatrixTail M j s) (complexGeneralLinearHaar (t + 1)) ∧
      ∀ (g z : G (t + 1)) (w : G (r + 1 - (t + 1))) (X : Mat (t + 1) (r + 1 - (t + 1)))
        (Y : Mat (r + 1 - (t + 1)) (t + 1)) (v : K (r + 1)),
      ordinaryGapNorm h Φ Ξ Ψ W.val V.val u s b g z w X Y v ≤
        C * Real.exp (-(A + 1) * ∑ i, |alpha g i|) * weightedMatrixTail M j s z *
          (δ w ^ (r + 1 - (t + 1)) * matrixDecay p w.val) * matrixDecay q X * matrixDecay l Y

set_option maxHeartbeats 1200000 in
theorem complexGapOrdinaryMajorant : ComplexGapOrdinaryMajorantStatement := by
  intro r t h ds es a W V A hA
  let n := r + 1
  let k := t + 1
  let d := n - k
  let hk : 0 < k := Nat.succ_pos t
  let hkn : k < n := Nat.succ_lt_succ h
  obtain ⟨N, hW⟩ := compact_rightTranslate_uniformSimpleRootBound W {1} isCompact_singleton
  obtain ⟨N', hV⟩ := complexWhittakerTranslateBound t es (-a) V
  obtain ⟨C₂, hC₂, hV₀⟩ := hV 0
  let M := N' * k
  let A₀ : ℝ := N + N' + A
  refine ⟨(A₀ + 1) / 2, (k : ℝ) + M, M, fun u s b hu hs Φ Ξ Ψ p q l => ?_⟩
  obtain ⟨j, hj⟩ := exists_integrable_weightedMatrixTail t M s hs
  obtain ⟨C₀, hC₀, hΦ⟩ := exists_leading_bound (Nat.add_sub_of_le hkn.le) (Nat.succ_pos r) Φ j l
  obtain ⟨C₃, hC₃, hH⟩ := height_tail_mul_det_bound hk hkn
  let β := b - (j + l : ℕ) - (d : ℝ)
  let B₀ : ℝ := N + 2 * |β|
  have hB₀ : 0 ≤ B₀ := by dsimp only [B₀]; positivity
  have hT : A₀ + 1 ≤ 2 * u := by linarith
  obtain ⟨J, C₄, hC₄, hTail⟩ := complexGapOrdinaryTailBound r k hk hkn A₀ B₀ (2 * u) hB₀ hT
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
  have hw := hWJ (1 : G n) (Set.mem_singleton 1) (padGL hkn.le g * B⁻¹)
  dsimp only at hw
  rw [mul_one, complexTwoBlockIwasawa n k hk hkn g w X v, sum_abs_blockLog] at hw
  have hv := hV₀ g z
  simp only [Nat.cast_zero, zero_mul, mul_zero, sub_zero, add_zero] at hv
  have hDg : δ g ^ u = Real.exp (2 * u * Sum) := by
    rw [normalizedDet_eq_exp, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    dsimp only [Sum, y]
    ring
  have hD : 0 < δ w := normalizedDet_pos w
  have hHB : H B ^ (j + l) * δ w ^ b = (H B * δ w) ^ (j + l) * δ w ^ (d : ℕ) * δ w ^ β := by
    rw [mul_pow]
    have he : δ w ^ (j + l : ℕ) * δ w ^ d * δ w ^ β = δ w ^ b := by
      rw [← Real.rpow_natCast (δ w) (j + l), ← Real.rpow_natCast (δ w) d, ← Real.rpow_add hD,
        ← Real.rpow_add hD]
      congr 1
      dsimp only [β]
      ring
    rw [← he]
    ring
  have hHB' : H B ^ (j + l) * δ w ^ b ≤ C₃ ^ (j + l) * S ^ m * δ w ^ d *
      Real.exp (2 * |β| * Sz) := by
    rw [hHB]
    refine mul_le_mul (mul_le_mul_of_nonneg_right (hH (j + l) w X v) (pow_nonneg hD.le _))
      (normalizedDet_rpow_inv_le w β) (Real.rpow_nonneg hD.le _) (by dsimp only [S, m]; positivity)
  have hF := hΦ B z.val Y
  have hE : Real.exp ((N : ℝ) * (Sy + Sz) - (J : ℝ) * rootPos x) * Real.exp ((N' : ℝ) * Sy) *
      Real.exp (2 * u * Sum) * Real.exp (2 * |β| * Sz) =
        Real.exp (-A * Sy) * Real.exp (A₀ * Sy + B₀ * Sz + (2 * u) * Sum - (J : ℝ) * rootPos x) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [A₀, B₀]
    ring
  have hH' : 0 ≤ H z := zero_le_two.trans (two_le_complexMatrixHeight hk z)
  have hY : 0 ≤ matrixDecay l Y := by unfold matrixDecay; positivity
  have hz : 0 ≤ matrixDecay j z.val := by unfold matrixDecay; positivity
  have hb : 0 ≤ δ z ^ s := Real.rpow_nonneg (normalizedDet_pos z).le _
  have hM : 0 ≤ weightedMatrixTail M j s z := by unfold weightedMatrixTail; positivity
  have hMajor := hTail y w X v
  change D * S ^ m * _ ≤ C₄ * Real.exp (-Sy) * matrixDecay p w.val * matrixDecay q X at hMajor
  dsimp only [ordinaryGapNorm]
  change ‖Φ (B.val * leadingInput (Nat.add_sub_of_le hkn.le) z.val Y)‖ * D *
    ‖W.val (padGL hkn.le g * B⁻¹)‖ * ‖V.val (g * z)‖ * δ g ^ u * δ z ^ s * δ w ^ b ≤ _
  rw [hDg]
  calc
    _ ≤ (C₀ * H B ^ (j + l) * matrixDecay j z.val * matrixDecay l Y) * D *
        (C₁ * Real.exp ((N : ℝ) * (Sy + Sz) - (J : ℝ) * rootPos x)) *
        (C₂ * H z ^ M * Real.exp ((N' : ℝ) * Sy)) * Real.exp (2 * u * Sum) * δ z ^ s * δ w ^ b := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hF (norm_nonneg _)) hw (norm_nonneg _) ?_)
          hv (norm_nonneg _) ?_) (Real.exp_nonneg _)) hb) (Real.rpow_nonneg hD.le _)
      · exact mul_nonneg ((norm_nonneg _).trans hF) (by dsimp only [D]; positivity)
      · exact mul_nonneg (mul_nonneg ((norm_nonneg _).trans hF) (by dsimp only [D]; positivity))
          (mul_nonneg hC₁ (Real.exp_nonneg _))
    _ = (C₀ * C₁ * C₂ * Real.exp ((N : ℝ) * (Sy + Sz) - (J : ℝ) * rootPos x) *
          Real.exp ((N' : ℝ) * Sy) * Real.exp (2 * u * Sum) * weightedMatrixTail M j s z *
          matrixDecay l Y * D) * (H B ^ (j + l) * δ w ^ b) := by unfold weightedMatrixTail; ring
    _ ≤ (C₀ * C₁ * C₂ * Real.exp ((N : ℝ) * (Sy + Sz) - (J : ℝ) * rootPos x) *
          Real.exp ((N' : ℝ) * Sy) * Real.exp (2 * u * Sum) * weightedMatrixTail M j s z *
          matrixDecay l Y * D) * (C₃ ^ (j + l) * S ^ m * δ w ^ d * Real.exp (2 * |β| * Sz)) :=
      mul_le_mul_of_nonneg_left hHB' (by dsimp only [D]; positivity)
    _ = (C₀ * C₁ * C₂ * C₃ ^ (j + l) * Real.exp (-A * Sy) * weightedMatrixTail M j s z *
        δ w ^ d * matrixDecay l Y) * (D * S ^ m *
          Real.exp (A₀ * Sy + B₀ * Sz + (2 * u) * Sum - (J : ℝ) * rootPos x)) := by
      calc
        _ = (C₀ * C₁ * C₂ * C₃ ^ (j + l) * weightedMatrixTail M j s z * δ w ^ d * matrixDecay l Y *
              D * S ^ m) * (Real.exp ((N : ℝ) * (Sy + Sz) - (J : ℝ) * rootPos x) * Real.exp ((N' : ℝ) * Sy) *
              Real.exp (2 * u * Sum) * Real.exp (2 * |β| * Sz)) := by ring
        _ = _ := by rw [hE]; ring
    _ ≤ (C₀ * C₁ * C₂ * C₃ ^ (j + l) * Real.exp (-A * Sy) * weightedMatrixTail M j s z *
          δ w ^ d * matrixDecay l Y) * (C₄ * Real.exp (-Sy) * matrixDecay p w.val * matrixDecay q X) :=
      mul_le_mul_of_nonneg_left hMajor (by positivity)
    _ = _ := by
      rw [show -(A + 1) * Sy = -A * Sy + (-Sy) by ring, Real.exp_add]
      ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapOrdinaryMajorant
