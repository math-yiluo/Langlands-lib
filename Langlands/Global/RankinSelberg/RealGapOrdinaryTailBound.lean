import Langlands.Global.RankinSelberg.RealGapTailMatrix
import Langlands.Global.RankinSelberg.RealGapTorusBound
import Langlands.Global.RankinSelberg.RealGapLeadingSchwartz

/-! # Joint ordinary-tail domination in the real gap recurrence -/

noncomputable section

open scoped NNReal Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapOrdinaryTailBound

open Langlands.Archimedean (unitaryCompact)
open RealTwoBlockHaar (rightTail tailColumns rightTail_norm_bounds blockLog realTwoBlockIwasawa)
open RealGapTorusBound (blockLog_last exponent_le)
open RealGapLeadingSchwartz (matrixDecay)
open RealIwasawa (alpha bpart bpart_iwasawa exp_alpha kpart npart npart_mul_torus_mul_kpart torus torus_neg
  torus_val)
open RealGapLeadingSchwartz (norm_entry_le_opNorm)
open RealConvergenceAnalysis (rootPos)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "K" => fun n => unitaryCompact ℝ n
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℝ
local notation "Row" => fun n => Fin n → ℝ

private theorem norm_mul_entry_le {n : ℕ} (A B : Mat n n) (i j : Fin n) {a b : ℝ}
    (ha : 0 ≤ a) (hA : ∀ l, ‖A i l‖ ≤ a) (hB : ∀ l, ‖B l j‖ ≤ b) :
    ‖(A * B) i j‖ ≤ (n : ℝ) * (a * b) := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ l, ‖A i l * B l j‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin n, a * b := Finset.sum_le_sum fun l _ => by
      rw [norm_mul]
      exact mul_le_mul (hA l) (hB l) (norm_nonneg _) ha
    _ = _ := by simp [nsmul_eq_mul]

/-- The entrywise supremum norm of a real matrix (the norm of the underlying function). -/
def entrySup {m n : ℕ} (X : Mat m n) : ℝ := ‖(show Fin m → Fin n → ℝ from X)‖

theorem entrySup_nonneg {m n : ℕ} (X : Mat m n) : 0 ≤ entrySup X := norm_nonneg _

theorem norm_entry_le_entrySup {m n : ℕ} (X : Mat m n) (i : Fin m) (j : Fin n) :
    ‖X i j‖ ≤ entrySup X :=
  (norm_le_pi_norm (X i) j).trans (norm_le_pi_norm (show Fin m → Fin n → ℝ from X) i)

/-- The entrywise supremum is bounded by the row-sum operator norm. -/
theorem entrySup_le_opNorm {m n : ℕ} (X : Mat m n) : entrySup X ≤ ‖X‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg X)).mpr fun i =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg X)).mpr fun j => norm_entry_le_opNorm X i j

/-- The row-sum operator norm is at most the number of columns times the entrywise supremum. -/
theorem opNorm_le_entrySup {m n : ℕ} (X : Mat m n) : ‖X‖ ≤ (n : ℝ) * entrySup X := by
  have hX : ‖X‖₊ ≤ (n : ℝ≥0) * ⟨entrySup X, entrySup_nonneg X⟩ := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ => ?_
    calc
      ∑ j, ‖X i j‖₊ ≤ ∑ _j : Fin n, (⟨entrySup X, entrySup_nonneg X⟩ : ℝ≥0) :=
        Finset.sum_le_sum fun j _ => by
          rw [← NNReal.coe_le_coe, coe_nnnorm]
          exact norm_entry_le_entrySup X i j
      _ = _ := by simp
  have := NNReal.coe_le_coe.mpr hX
  rw [coe_nnnorm, NNReal.coe_mul, NNReal.coe_natCast] at this
  exact this

private theorem exp_neg_alpha_inv_le {n : ℕ} (h : G n) (i : Fin n) :
    Real.exp (-alpha h⁻¹ i) ≤ (n : ℝ) * entrySup h.val := by
  let g := h⁻¹
  have hb : bpart g = (npart g).val * torus (alpha g) := by
    conv_lhs => rw [← npart_mul_torus_mul_kpart g]
    rw [bpart_iwasawa]
  have hd : (bpart g)⁻¹.val i i = Real.exp (-alpha g i) := by
    rw [hb, mul_inv_rev, Units.val_mul, ← torus_neg, torus_val, Matrix.diagonal_mul]
    have he : (npart g).val⁻¹.val i i = 1 :=
      Langlands.GeneralLinear.UpperUnipotent.entry_diag (npart g)⁻¹ i
    rw [he, mul_one]
    rfl
  have he : (bpart g)⁻¹ = (kpart g).val * h := by rw [bpart, mul_inv_rev, inv_inv]; rfl
  have hm := norm_mul_entry_le (kpart g).val.val h.val i i zero_le_one
    (fun j => LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup (kpart g).2 i j)
    (fun j => norm_entry_le_entrySup h.val j i)
  change ‖((kpart g).val * h).val i i‖ ≤ _ at hm
  rw [← he, hd, Real.norm_of_nonneg (Real.exp_nonneg _), one_mul] at hm
  exact hm

private theorem exp_alpha_last_le {r : ℕ} (g : G (r + 1)) :
    Real.exp (alpha g (Fin.last r)) ≤ (r + 1 : ℕ) * ‖g.val (Fin.last r)‖ := by
  let i := Fin.last r
  have hm := norm_mul_entry_le g.val ((kpart g)⁻¹).val.val i i (norm_nonneg (g.val i))
    (fun j => norm_le_pi_norm (g.val i) j)
    (fun j => LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup ((kpart g)⁻¹).2 j i)
  change ‖(bpart g).val i i‖ ≤ _ at hm
  rw [← exp_alpha, Real.norm_of_nonneg (Real.exp_nonneg _), mul_one] at hm
  exact hm

/-- The required root decay and determinant weight leave only a polynomial cost in the
full tail columns and last inverse row, and an integrable exponential in the first torus. -/
theorem exists_ordinaryTail_exponential_bound {r k : ℕ} (hk : 0 < k) (hkn : k < r + 1)
    (A B T : ℝ) (hB : 0 ≤ B) (hT : A + 1 ≤ T) :
    ∃ J p q : ℕ, ∀ (y : Fin k → ℝ) (h : G (r + 1 - k)) (X : Mat k (r + 1 - k)) (v : K (r + 1)),
      let g := rightTail hk hkn h X v
      let z := alpha h⁻¹
      let x := blockLog hkn y z
      Real.exp (A * (∑ i, |y i|) + B * (∑ i, |z i|) + T * (∑ i, y i) - (J : ℝ) * rootPos x) ≤
        Real.exp (-∑ i, |y i|) *
          (((r + 1 : ℕ) : ℝ) ^ 2 * (1 + ‖tailColumns hkn g‖)) ^ p *
          (((r + 1 : ℕ) : ℝ) * (1 + ‖g⁻¹.val (Fin.last r)‖)) ^ q := by
  let n : ℝ := (r + 1 : ℕ)
  let d : ℝ := (r + 1 - k : ℕ)
  let P := max (2 * T) (B + 1) * ((r : ℝ) + 1)
  let Q := B + 1
  have hn : 1 ≤ n := by dsimp only [n]; exact_mod_cast Nat.succ_pos r
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hdn : d ≤ n := by dsimp only [d, n]; exact_mod_cast Nat.sub_le (r + 1) k
  have hP : 0 ≤ P := mul_nonneg (zero_le_one.trans (by linarith [le_max_right (2 * T) (B + 1)]))
    (by positivity)
  have hQ : 0 ≤ Q := by dsimp only [Q]; linarith
  obtain ⟨J, hJ⟩ := exists_nat_ge P
  obtain ⟨p, hp⟩ := exists_nat_ge (Q * d)
  obtain ⟨q, hq⟩ := exists_nat_ge P
  refine ⟨J, p, q, fun y h X v => ?_⟩
  let g := rightTail hk hkn h X v
  let z := alpha h⁻¹
  let x := blockLog hkn y z
  let C := n ^ 2 * (1 + ‖tailColumns hkn g‖)
  let D := n * (1 + ‖g⁻¹.val (Fin.last r)‖)
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn)
    (le_add_of_nonneg_right (norm_nonneg _))
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le hn (le_add_of_nonneg_right (norm_nonneg _))
  have hC₀ := zero_lt_one.trans_le hC
  have hD₀ := zero_lt_one.trans_le hD
  have hTail : entrySup h.val ≤ n * ‖tailColumns hkn g‖ :=
    ((rightTail_norm_bounds hk hkn h X v).1 : entrySup h.val ≤ n * entrySup (tailColumns hkn g)).trans
      (mul_le_mul_of_nonneg_left (entrySup_le_opNorm _) (zero_le_one.trans hn))
  have hnz (i : Fin (r + 1 - k)) : max (-z i) 0 ≤ Real.log C := by
    refine max_le ?_ (Real.log_nonneg hC)
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hC₀]
    calc
      _ ≤ d * entrySup h.val := exp_neg_alpha_inv_le h i
      _ ≤ n * (n * ‖tailColumns hkn g‖) := mul_le_mul hdn hTail (entrySup_nonneg _) (zero_le_one.trans hn)
      _ ≤ C := by dsimp only [C]; rw [pow_two, ← mul_assoc]; gcongr; exact le_add_of_nonneg_left zero_le_one
  have hnSum : (∑ i, max (-z i) 0) ≤ d * Real.log C := by
    calc
      _ ≤ ∑ _ : Fin (r + 1 - k), Real.log C := Finset.sum_le_sum fun i _ => hnz i
      _ = _ := by simp [nsmul_eq_mul, d]
  have hAlpha : alpha g⁻¹ = blockLog hkn (alpha (1 : G k)) z := by
    simpa only [map_one, one_mul] using realTwoBlockIwasawa (r + 1) k hk hkn (1 : G k) h X v
  have hLast : x (Fin.last r) = alpha g⁻¹ (Fin.last r) := by
    rw [hAlpha]
    exact (blockLog_last hkn y z).trans (blockLog_last hkn (alpha (1 : G k)) z).symm
  have hLastD : max (x (Fin.last r)) 0 ≤ Real.log D := by
    refine max_le ?_ (Real.log_nonneg hD)
    rw [hLast]
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hD₀]
    exact (exp_alpha_last_le g⁻¹).trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left zero_le_one) (zero_le_one.trans hn))
  have hE := exponent_le hkn y z hB hT hJ (P := P) le_rfl (Q := Q) le_rfl
  have h₁ := mul_le_mul_of_nonneg_left hnSum hQ
  have h₂ := mul_le_mul_of_nonneg_left hLastD hP
  have h₃ := mul_le_mul_of_nonneg_right hp (Real.log_nonneg hC)
  have h₄ := mul_le_mul_of_nonneg_right hq (Real.log_nonneg hD)
  have hExp : A * (∑ i, |y i|) + B * (∑ i, |z i|) + T * (∑ i, y i) - (J : ℝ) * rootPos x ≤
      -(∑ i, |y i|) + (p : ℝ) * Real.log C + (q : ℝ) * Real.log D := by
    dsimp only at hE
    change A * (∑ i, |y i|) + B * (∑ i, |z i|) + T * (∑ i, y i) - (J : ℝ) * rootPos x -
      P * max (x (Fin.last r)) 0 - Q * (∑ i, max (-z i) 0) ≤ _ at hE
    have hs : 0 ≤ ∑ i, |z i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith only [hE, h₁, h₂, h₃, h₄, hs]
  dsimp only
  refine (Real.exp_le_exp.mpr hExp).trans_eq ?_
  rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hC₀,
    Real.exp_log hD₀]

/-- After the tail column and inverse row Schwartz factors are inserted, the ordinary gap
kernel has separate decay in the tail matrix and upper rectangle. The extra polynomial
power allows the height contribution of the leading test to be included. -/
def RealGapOrdinaryTailBoundStatement : Prop :=
  ∀ (r k : ℕ) (hk : 0 < k) (hkn : k < r + 1) (A B T : ℝ), 0 ≤ B → A + 1 ≤ T →
    ∀ (Φ : 𝓢(Mat (r + 1) (r + 1 - k), ℂ)) (Ψ : 𝓢(Row (r + 1), ℂ)) (m p q : ℕ),
      ∃ (J : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (y : Fin k → ℝ) (h : G (r + 1 - k)) (X : Mat k (r + 1 - k)) (v : K (r + 1)),
        let g := rightTail hk hkn h X v
        let z := alpha h⁻¹
        let x := blockLog hkn y z
        ‖Φ (tailColumns hkn g) * Ψ (g⁻¹.val (Fin.last r))‖ * (1 + ‖tailColumns hkn g‖) ^ m *
          Real.exp (A * (∑ i, |y i|) + B * (∑ i, |z i|) + T * (∑ i, y i) - (J : ℝ) * rootPos x) ≤
          C * Real.exp (-∑ i, |y i|) * matrixDecay p h.val * matrixDecay q X

theorem realGapOrdinaryTailBound : RealGapOrdinaryTailBoundStatement := by
  intro r k hk hkn A B T hB hT Φ Ψ m p q
  obtain ⟨J, p₀, q₀, hE⟩ := exists_ordinaryTail_exponential_bound hk hkn A B T hB hT
  let n : ℝ := (r + 1 : ℕ)
  let L := m + p₀ + (p + q)
  let S₁ : Seminorm ℝ 𝓢(Mat (r + 1) (r + 1 - k), ℂ) :=
    (Finset.Iic (L, 0)).sup (fun a => SchwartzMap.seminorm ℝ a.1 a.2)
  let S₂ : Seminorm ℝ 𝓢(Row (r + 1), ℂ) :=
    (Finset.Iic (q₀, 0)).sup (fun a => SchwartzMap.seminorm ℝ a.1 a.2)
  let C₁ := (2 : ℝ) ^ L * S₁ Φ
  let C₂ := (2 : ℝ) ^ q₀ * S₂ Ψ
  have hn : 1 ≤ n := by dsimp only [n]; exact_mod_cast Nat.succ_pos r
  have hC₁ : 0 ≤ C₁ := mul_nonneg (by positivity) (apply_nonneg _ _)
  have hC₂ : 0 ≤ C₂ := mul_nonneg (by positivity) (apply_nonneg _ _)
  let C := (n ^ 2) ^ p₀ * n ^ q₀ * (n ^ 2) ^ (p + q) * C₁ * C₂
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨J, C, hC, fun y h X v => ?_⟩
  let g := rightTail hk hkn h X v
  let S := 1 + ‖tailColumns hkn g‖
  let U := 1 + ‖g⁻¹.val (Fin.last r)‖
  let E := Real.exp (-∑ i, |y i|)
  let F := ‖Φ (tailColumns hkn g)‖
  let G' := ‖Ψ (g⁻¹.val (Fin.last r))‖
  let V := 1 + ‖h.val‖
  let W := 1 + ‖X‖
  have hF : S ^ L * F ≤ C₁ := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (L, 0)) le_rfl le_rfl Φ
      (tailColumns hkn g)
    simpa only [norm_iteratedFDeriv_zero, S, F, C₁, S₁] using h
  have hG : U ^ q₀ * G' ≤ C₂ := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (q₀, 0)) le_rfl le_rfl Ψ
      (g⁻¹.val (Fin.last r))
    simpa only [norm_iteratedFDeriv_zero, U, G', C₂, S₂] using h
  obtain ⟨hV, hW, _⟩ := rightTail_norm_bounds hk hkn h X v
  have hV' : entrySup h.val ≤ n * entrySup (tailColumns hkn g) := hV
  have hW' : entrySup X ≤ n * entrySup (tailColumns hkn g) := hW
  have hT : entrySup (tailColumns hkn g) ≤ ‖tailColumns hkn g‖ := entrySup_le_opNorm _
  have hd : ((r + 1 - k : ℕ) : ℝ) ≤ n := by dsimp only [n]; exact_mod_cast Nat.sub_le (r + 1) k
  have hn₀ : 0 ≤ n := zero_le_one.trans hn
  have hn₂ : 1 ≤ n ^ 2 := one_le_pow₀ hn
  have hNorm {m' : ℕ} (Z : Mat m' (r + 1 - k)) (hZ : entrySup Z ≤ n * entrySup (tailColumns hkn g)) :
      1 + ‖Z‖ ≤ n ^ 2 * S := by
    have h₀ : ‖Z‖ ≤ n ^ 2 * ‖tailColumns hkn g‖ := by
      refine (opNorm_le_entrySup Z).trans ?_
      calc
        ((r + 1 - k : ℕ) : ℝ) * entrySup Z ≤ n * (n * entrySup (tailColumns hkn g)) :=
          mul_le_mul hd hZ (entrySup_nonneg _) hn₀
        _ ≤ n * (n * ‖tailColumns hkn g‖) := by gcongr
        _ = _ := by ring
    dsimp only [S]
    rw [mul_add, mul_one]
    exact add_le_add hn₂ h₀
  have h₁ : V ≤ n ^ 2 * S := hNorm h.val hV'
  have h₂ : W ≤ n ^ 2 * S := hNorm X hW'
  have hVW : V ^ p * W ^ q ≤ (n ^ 2 * S) ^ (p + q) := by
    rw [pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (by dsimp only [V]; positivity) h₁ _)
      (pow_le_pow_left₀ (by dsimp only [W]; positivity) h₂ _) (by dsimp only [W]; positivity) (by positivity)
  have hpos : 0 < V ^ p * W ^ q := by dsimp only [V, W]; positivity
  have hF' : 0 ≤ F := norm_nonneg _
  have hG' : 0 ≤ G' := norm_nonneg _
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  dsimp only
  rw [norm_mul]
  change F * G' * S ^ m * _ ≤ C * E * (V ^ p)⁻¹ * (W ^ q)⁻¹
  rw [mul_assoc (C * E), ← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ hpos).mpr
  calc
    _ ≤ F * G' * S ^ m * (E * (n ^ 2 * S) ^ p₀ * (n * U) ^ q₀) * (V ^ p * W ^ q) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hE y h X v) (by positivity)) hpos.le
    _ ≤ F * G' * S ^ m * (E * (n ^ 2 * S) ^ p₀ * (n * U) ^ q₀) * (n ^ 2 * S) ^ (p + q) := by
      exact mul_le_mul_of_nonneg_left hVW (by dsimp only [E]; positivity)
    _ = ((n ^ 2) ^ p₀ * n ^ q₀ * (n ^ 2) ^ (p + q) * E) * (S ^ L * F) * (U ^ q₀ * G') := by
      rw [mul_pow, mul_pow, mul_pow]
      dsimp only [L]
      rw [pow_add S (m + p₀), pow_add S m p₀]
      ring
    _ ≤ ((n ^ 2) ^ p₀ * n ^ q₀ * (n ^ 2) ^ (p + q) * E) * C₁ * C₂ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hF (by dsimp only [E]; positivity)) hG (by positivity)
        (by dsimp only [E]; positivity)
    _ = _ := by dsimp only [C]; ring

end Langlands.Global.RankinSelbergGlobal.RealGapOrdinaryTailBound
