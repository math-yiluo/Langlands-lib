import Langlands.Global.RankinSelberg.ComplexGapTorusBound
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Schwartz decay at the endpoints of the complex right tail -/

noncomputable section

open scoped SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapTailEndpoints

open Langlands.Archimedean (unitaryCompact)
open Langlands.ProductLeviChamber (twoBlock twoBlock_index_val)
open ComplexTwoBlockHaar (rectangleCoordinates leviBlocks rightTail)
open ComplexLocalWhittakerGauge (logTorus logTorus_val logTorus_inv_val)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "K" => fun n => unitaryCompact ℂ n
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "R" => fun n k => Matrix (Fin k) (Fin (n - k)) ℂ
local notation "Row" => fun n => Fin n → ℂ

private def firstTail {r k : ℕ} (hkn : k < r + 1) : Fin (r + 1 - k) :=
  ⟨0, Nat.sub_pos_of_lt hkn⟩

private def lastTail {r k : ℕ} (hkn : k < r + 1) : Fin (r + 1 - k) :=
  ⟨r - k, by omega⟩

section

variable {r k : ℕ} (hk : 0 < k) (hkn : k < r + 1)

local notation "n" => r + 1
local notation "d" => r + 1 - k
local notation "B" => twoBlock n k hk hkn
local notation "fstTail" => (firstTail hkn)
local notation "lstTail" => (lastTail hkn)

/-- The first column in the trailing block, evaluated in the ambient group. -/
def firstTailColumn (g : G n) : Row n :=
  fun i => g.val i ((B).index (1 : Fin 2) fstTail)

private theorem last_tail_index : (B).index (1 : Fin 2) lstTail = Fin.last r := by
  apply Fin.ext
  rw [twoBlock_index_val]
  change k + (r - k) = r
  omega

set_option maxHeartbeats 800000 in
private theorem remove_tail_unitary (h : G d) (X : R n k) (q : K n) (i j : Fin d) :
    (q.val⁻¹ * rightTail hk hkn h X q).val ((B).index (1 : Fin 2) i) ((B).index (1 : Fin 2) j) = h.val i j ∧
      ((rightTail hk hkn h X q)⁻¹ * q.val).val ((B).index (1 : Fin 2) i) ((B).index (1 : Fin 2) j) =
        h⁻¹.val i j := by
  let S := B
  let m : S.Levi ℂ := (leviBlocks hk hkn).symm ((1 : G k), h)
  let u : S.unipotentRadical ℂ := (rectangleCoordinates hk hkn).symm X
  let b : S.parabolic ℂ := S.leviInParabolic ℂ m * u.val
  have hb : b.val = S.leviEmbedding ℂ m * u.val.val := by
    change (S.leviInParabolic ℂ m).val * u.val.val = _
    rw [S.leviInParabolic_val ℂ]
  have hG : rightTail hk hkn h X q = q.val * b.val := by
    change q.val * S.leviEmbedding ℂ m * u.val.val = _
    rw [hb, mul_assoc]
  have hp : S.leviProjection ℂ b = m := by
    dsimp only [b]
    rw [map_mul (S.leviProjection ℂ), S.leviProjection_section ℂ,
      show S.leviProjection ℂ u.val = 1 from u.2, mul_one]
  have hpi : S.leviProjection ℂ b⁻¹ = m⁻¹ := by rw [map_inv, hp]
  have hm : m (1 : Fin 2) = h := rfl
  have hmi : m⁻¹ (1 : Fin 2) = h⁻¹ := by
    change (m (1 : Fin 2))⁻¹ = _
    rw [hm]
  rw [hG, inv_mul_cancel_left, mul_inv_rev, inv_mul_cancel_right]
  constructor
  · have he := congrArg (fun a : S.Levi ℂ => (a (1 : Fin 2)).val i j) hp
    simpa only [S.leviProjection_apply, hm, S] using he
  · have he := congrArg (fun a : S.Levi ℂ => (a (1 : Fin 2)).val i j) hpi
    simpa only [S.leviProjection_apply, hmi, Subgroup.coe_inv, S] using he

private theorem norm_unitary_col_le (q : K n) (g : G n) (i j : Fin n) :
    ‖(q.val * g).val i j‖ ≤ (n : ℕ) * ‖fun b => g.val b j‖ := by
  change ‖∑ b : Fin n, q.val.val i b * g.val b j‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin n, ‖fun b => g.val b j‖ := by
      refine Finset.sum_le_sum fun b _ => ?_
      rw [norm_mul, ← one_mul ‖fun b => g.val b j‖]
      exact mul_le_mul (LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup q.2 i b)
        (norm_le_pi_norm (fun b => g.val b j) b) (norm_nonneg _) zero_le_one
    _ = _ := by simp [nsmul_eq_mul]

private theorem norm_row_unitary_le (q : K n) (g : G n) (i j : Fin n) :
    ‖(g * q.val).val i j‖ ≤ (n : ℕ) * ‖g.val i‖ := by
  change ‖∑ b : Fin n, g.val i b * q.val.val b j‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin n, ‖g.val i‖ := by
      refine Finset.sum_le_sum fun b _ => ?_
      rw [norm_mul, ← mul_one ‖g.val i‖]
      exact mul_le_mul (norm_le_pi_norm (g.val i) b)
        (LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup q.2 b j)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [nsmul_eq_mul]

/-- The norms of the first tail column and last inverse row detect the two logarithmic
endpoints, uniformly in the upper rectangle, upper unipotent tail, and left unitary factor. -/
theorem exp_le_endpoint_norms (z : Fin d → ℝ) (u : N d) (X : R n k) (q : K n) :
    let g := rightTail hk hkn (logTorus (-z) * u.val) X q
    Real.exp (-z fstTail) ≤ (n : ℕ) * ‖firstTailColumn hk hkn g‖ ∧
      Real.exp (z lstTail) ≤ (n : ℕ) * ‖g⁻¹.val (Fin.last r)‖ := by
  let h := logTorus (-z) * u.val
  let g := rightTail hk hkn h X q
  have h₁ : h.val fstTail fstTail = (Real.exp (-z fstTail) : ℂ) := by
    rw [show h.val = (logTorus (-z)).val * u.val.val from rfl, logTorus_val, Matrix.diagonal_mul,
      Langlands.GeneralLinear.UpperUnipotent.entry_diag u fstTail, mul_one]
    rfl
  have h₂ : h⁻¹.val lstTail lstTail = (Real.exp (z lstTail) : ℂ) := by
    dsimp only [h]
    rw [mul_inv_rev, Units.val_mul, logTorus_inv_val, Matrix.mul_diagonal]
    have h' : u.val⁻¹.val lstTail lstTail = 1 :=
      Langlands.GeneralLinear.UpperUnipotent.entry_diag u⁻¹ lstTail
    rw [h', one_mul, Pi.neg_apply, neg_neg]
  have hf := (remove_tail_unitary hk hkn h X q fstTail fstTail).1.trans h₁
  have hh := (remove_tail_unitary hk hkn h X q lstTail lstTail).2.trans h₂
  rw [last_tail_index hk hkn] at hh
  have hf' := congrArg norm hf
  have hh' := congrArg norm hh
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)] at hf' hh'
  change _ ≤ (n : ℕ) * ‖firstTailColumn hk hkn g‖ ∧ _ ≤ (n : ℕ) * ‖g⁻¹.val (Fin.last r)‖
  constructor
  · rw [← hf']
    exact norm_unitary_col_le q⁻¹ g _ _
  · rw [← hh']
    exact norm_row_unitary_le q g⁻¹ _ _

private theorem exists_schwartz_endpoint_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : 𝓢(E, ℂ)) (D : ℝ) (hD : 1 ≤ D) (P : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : E) (t : ℝ), Real.exp t ≤ D * ‖x‖ →
      ‖F x‖ ≤ C * Real.exp (-P * max t 0) := by
  obtain ⟨j, hj⟩ := exists_nat_ge P
  let c₀ := SchwartzMap.seminorm ℝ 0 0 F
  let c₁ := D ^ j * SchwartzMap.seminorm ℝ j 0 F
  have hc₀ : 0 ≤ c₀ := apply_nonneg _ _
  have hc₁ : 0 ≤ c₁ := mul_nonneg (pow_nonneg (zero_le_one.trans hD) _) (apply_nonneg _ _)
  refine ⟨max c₀ c₁, hc₀.trans (le_max_left _ _), fun x t ht => ?_⟩
  rcases le_total 0 t with ht₀ | ht₀
  · rw [max_eq_left ht₀]
    have hp := pow_le_pow_left₀ (Real.exp_nonneg _) ht j
    rw [mul_pow, ← Real.exp_nat_mul] at hp
    have hf : ‖F x‖ * Real.exp ((j : ℝ) * t) ≤ c₁ := by
      calc
        _ ≤ ‖F x‖ * (D ^ j * ‖x‖ ^ j) := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
        _ = D ^ j * (‖x‖ ^ j * ‖F x‖) := by ring
        _ ≤ c₁ := mul_le_mul_of_nonneg_left (F.norm_pow_mul_le_seminorm ℝ j x)
          (pow_nonneg (zero_le_one.trans hD) _)
    have hF : ‖F x‖ ≤ c₁ * Real.exp (-(j : ℝ) * t) := by
      rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
      exact (le_div_iff₀ (Real.exp_pos _)).mpr hf
    exact hF.trans (mul_le_mul (le_max_right _ _)
      (Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right hj ht₀]))
      (Real.exp_nonneg _) (hc₀.trans (le_max_left _ _)))
  · rw [max_eq_right ht₀, mul_zero, Real.exp_zero, mul_one]
    exact (F.norm_le_seminorm ℝ x).trans (le_max_left _ _)

end

/-- The two endpoint Schwartz tests give arbitrary decay in the negative part of the first
and the positive part of the last logarithmic tail coordinate. -/
def ComplexGapTailEndpointsStatement : Prop :=
  ∀ (r k : ℕ) (hk : 0 < k) (hkn : k < r + 1)
    (Φ Ψ : 𝓢(Row (r + 1), ℂ)) (P Q : ℝ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Fin (r + 1 - k) → ℝ) (u : N (r + 1 - k))
      (X : R (r + 1) k) (q : K (r + 1)),
      let g := rightTail hk hkn (logTorus (-z) * u.val) X q
      ‖Φ (firstTailColumn hk hkn g) * Ψ (g⁻¹.val (Fin.last r))‖ ≤
        C * Real.exp (-P * max (-z ⟨0, Nat.sub_pos_of_lt hkn⟩) 0 - Q * max (z ⟨r - k, by omega⟩) 0)

theorem complexGapTailEndpoints : ComplexGapTailEndpointsStatement := by
  intro r k hk hkn Φ Ψ P Q
  have hR : 1 ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos r
  obtain ⟨C₁, hC₁, hΦ⟩ := exists_schwartz_endpoint_bound Φ _ hR P
  obtain ⟨C₂, hC₂, hΨ⟩ := exists_schwartz_endpoint_bound Ψ _ hR Q
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, fun z u X q => ?_⟩
  let g := rightTail hk hkn (logTorus (-z) * u.val) X q
  obtain ⟨hf, hh⟩ := exp_le_endpoint_norms hk hkn z u X q
  have h₁ := hΦ (firstTailColumn hk hkn g) _ hf
  have h₂ := hΨ (g⁻¹.val (Fin.last r)) _ hh
  dsimp only
  simp only [firstTail, lastTail] at h₁ h₂
  rw [norm_mul, sub_eq_add_neg, ← neg_mul Q, Real.exp_add]
  refine (mul_le_mul h₁ h₂ (norm_nonneg _) (mul_nonneg hC₁ (Real.exp_nonneg _))).trans_eq ?_
  ac_rfl

end Langlands.Global.RankinSelbergGlobal.ComplexGapTailEndpoints
