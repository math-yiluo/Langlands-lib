import Langlands.Group.InternalPolarFactors
import Langlands.Representation.Archimedean.GeneralLinear
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-! # Polynomial operator growth of archimedean general linear representations -/

noncomputable section

open Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

universe uF uE

section UnitHeight

variable {A : Type*} [NormedRing A]

/-- The maximum of one and the norms of a unit and its inverse in the ambient ring. -/
def unitHeight (g : Aˣ) : ℝ := max 1 (max ‖g.val‖ ‖(g⁻¹ : Aˣ).val‖)

theorem one_le_unitHeight (g : Aˣ) : 1 ≤ unitHeight g := le_max_left _ _

theorem norm_val_le_unitHeight (g : Aˣ) : ‖g.val‖ ≤ unitHeight g :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem norm_inv_le_unitHeight (g : Aˣ) : ‖(g⁻¹ : Aˣ).val‖ ≤ unitHeight g :=
  (le_max_right _ _).trans (le_max_right _ _)

@[simp]
theorem unitHeight_inv (g : Aˣ) : unitHeight g⁻¹ = unitHeight g := by
  rw [unitHeight, unitHeight, inv_inv, max_comm ‖(g⁻¹ : Aˣ).val‖ ‖g.val‖]

theorem unitHeight_mul_le (g h : Aˣ) : unitHeight (g * h) ≤ unitHeight g * unitHeight h := by
  have hg := one_le_unitHeight g
  have hh := one_le_unitHeight h
  apply max_le (one_le_mul_of_one_le_of_one_le hg hh)
  apply max_le
  · rw [Units.val_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_val_le_unitHeight g)
      (norm_val_le_unitHeight h) (norm_nonneg _) (zero_le_one.trans hg))
  · rw [mul_inv_rev, Units.val_mul, mul_comm (unitHeight g) (unitHeight h)]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_inv_le_unitHeight h)
      (norm_inv_le_unitHeight g) (norm_nonneg _) (zero_le_one.trans hh))

theorem continuous_unitHeight : Continuous (unitHeight : Aˣ → ℝ) :=
  continuous_const.max (Units.continuous_val.norm.max Units.continuous_coe_inv.norm)

/-- A height sublevel set is compact when the ambient norm is proper. -/
theorem isCompact_unitHeight_sublevel [ProperSpace A] {C : ℝ} (hC : 1 ≤ C) :
    IsCompact {g : Aˣ | unitHeight g ≤ C} := by
  let K := Metric.closedBall (0 : A) C
  have hK : IsCompact K := isCompact_closedBall _ _
  have hp := Units.isClosedEmbedding_embedProduct (α := A) |>.isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert hp using 1
  ext g
  change unitHeight g ≤ C ↔ g.val ∈ K ∧ MulOpposite.op (g⁻¹ : Aˣ).val ∈ MulOpposite.op '' K
  simp [unitHeight, hC, K, Metric.mem_closedBall, dist_zero_right]

end UnitHeight

section GeneralLinear

open scoped ComplexOrder

open Langlands.Group.AlgebraicMatrixPowers Langlands.Group.AlgebraicPolar
open Langlands.Group.InternalPolarFactors Langlands.Group.MatrixPolarCompact
open Langlands.Group.PositivePowerPolynomial

variable (F : Type uF) [RCLike F] (n : ℕ)

local notation "GLₙ" => Langlands.GeneralLinear n F
local notation "Mat" => Matrix (Fin n) (Fin n) F

private theorem isCompact_unitaryCompact : IsCompact (unitaryCompact F n : Set GLₙ) := by
  have h := isCompact_unitarySubgroup (MonoidHom.id GLₙ) Topology.IsClosedEmbedding.id
  convert h using 1
  ext g
  exact (mem_unitarySubgroup (MonoidHom.id GLₙ) g).symm

private theorem exists_unitary_diagonal_factors (g : GLₙ) :
    ∃ (k l : GLₙ) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i),
      k ∈ unitaryCompact F n ∧ l ∈ unitaryCompact F n ∧
      g = k * diagonalPower a ha 1 * l := by
  have hpoly : IsPolynomiallyDefined (⊤ : Subgroup GLₙ) := ⟨∅, by simp⟩
  obtain ⟨k, x, -, -, hk, hx, hg⟩ := exists_unitary_posDef_factors (⊤ : Subgroup GLₙ) hpoly
    (by simp) g (by simp)
  let U : GLₙ := Unitary.toUnits hx.isHermitian.eigenvectorUnitary
  have hU : U ∈ unitaryCompact F n := hx.isHermitian.eigenvectorUnitary.property
  refine ⟨k * U, U⁻¹, hx.isHermitian.eigenvalues, hx.eigenvalues_pos,
    (unitaryCompact F n).mul_mem hk hU, (unitaryCompact F n).inv_mem hU, ?_⟩
  have he : x = U * diagonalPower hx.isHermitian.eigenvalues hx.eigenvalues_pos 1 * U⁻¹ :=
    (positivePower_one x hx).symm
  calc
    g = k * x := hg
    _ = k * (U * diagonalPower hx.isHermitian.eigenvalues hx.eigenvalues_pos 1 * U⁻¹) :=
      congrArg (k * ·) he
    _ = _ := by simp only [mul_assoc]

private theorem diagonalPower_height_le (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (t C : ℝ) (hC : 1 ≤ C) (hval : ∀ i, a i ^ t ≤ C) (hinv : ∀ i, (a i)⁻¹ ^ t ≤ C) :
    unitHeight (diagonalPower (𝕜 := F) a ha t) ≤ C := by
  apply max_le hC
  apply max_le
  · rw [diagonalPower_val, Matrix.linfty_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans hC)).mpr
    intro i
    simpa [powerPoint, RCLike.norm_ofReal, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (ha i).le _)] using hval i
  · rw [diagonalPower_inv_val, Matrix.linfty_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans hC)).mpr
    intro i
    simpa [Real.inv_rpow (ha i).le, powerPoint, RCLike.norm_ofReal, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (ha i).le _), norm_inv] using hinv i

private theorem diagonalPower_root_pow (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (m : ℕ) (hm : m ≠ 0) :
    diagonalPower (𝕜 := F) a ha (1 / (m : ℝ)) ^ m = diagonalPower a ha 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, diagonalPower_val, diagonalPower_val, Matrix.diagonal_pow]
  congr 1
  funext i
  change (RCLike.ofReal (a i ^ (1 / (m : ℝ))) : F) ^ m = RCLike.ofReal (a i ^ (1 : ℝ))
  rw [← RCLike.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul (ha i).le,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hm)]

private theorem exists_bounded_root_factors (C : ℝ) (hC : 1 ≤ C)
    (hK : ∀ k ∈ unitaryCompact F n, unitHeight k ≤ C) (g : GLₙ) :
    ∃ (k q l : GLₙ) (m : ℕ), unitHeight k ≤ C ∧ unitHeight l ≤ C ∧
      unitHeight q ≤ Real.exp 1 ∧ 0 < m ∧ (m : ℝ) ≤ Real.log (C ^ 2 * unitHeight g) + 2 ∧
      g = k * q ^ m * l := by
  obtain ⟨k, l, a, ha, hk, hl, hfac⟩ := exists_unitary_diagonal_factors F n g
  let d : GLₙ := diagonalPower a ha 1
  let M := C ^ 2 * unitHeight g
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) (one_le_unitHeight g)
  have hd : d = k⁻¹ * g * l⁻¹ := by
    rw [hfac]
    change d = k⁻¹ * (k * d * l) * l⁻¹
    group
  have hdM : unitHeight d ≤ M := by
    rw [hd]
    calc
      _ ≤ unitHeight (k⁻¹ * g) * unitHeight l⁻¹ := unitHeight_mul_le _ _
      _ ≤ ((C * unitHeight g) * C) := by
        rw [unitHeight_inv]
        have hkg := unitHeight_mul_le k⁻¹ g
        rw [unitHeight_inv] at hkg
        exact mul_le_mul (hkg.trans (mul_le_mul_of_nonneg_right (hK _ hk)
          (zero_le_one.trans (one_le_unitHeight g)))) (hK _ hl)
          (zero_le_one.trans (one_le_unitHeight l))
          (mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans (one_le_unitHeight g)))
      _ = M := by unfold M; ring
  have hai (i : Fin n) : a i ≤ M := by
    have h := norm_le_pi_norm (powerPoint (𝕜 := F) a 1) i
    rw [← Matrix.linfty_opNorm_diagonal] at h
    have h' := h.trans ((norm_val_le_unitHeight d).trans hdM)
    simpa [powerPoint, Real.rpow_one, RCLike.norm_ofReal, Real.norm_eq_abs,
      abs_of_pos (ha i)] using h'
  have hainv (i : Fin n) : (a i)⁻¹ ≤ M := by
    have h := norm_le_pi_norm (fun j => (powerPoint (𝕜 := F) a 1 j)⁻¹) i
    rw [← Matrix.linfty_opNorm_diagonal] at h
    have h' := h.trans ((norm_inv_le_unitHeight d).trans hdM)
    simpa [norm_inv, powerPoint, Real.rpow_one, RCLike.norm_ofReal, Real.norm_eq_abs,
      abs_of_pos (ha i)] using h'
  let m := ⌈Real.log M⌉₊ + 1
  have hm : 0 < m := Nat.succ_pos _
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmlo : Real.log M ≤ (m : ℝ) := by
    exact (Nat.le_ceil (Real.log M)).trans (by simp [m])
  have hmhi : (m : ℝ) ≤ Real.log M + 2 := by
    have hceil := Nat.ceil_lt_add_one (Real.log_nonneg hM)
    push_cast [m]
    linarith
  have hsmall (x : ℝ) (hx : 0 < x) (hxM : x ≤ M) : x ^ (1 / (m : ℝ)) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hx, mul_one_div, Real.exp_le_exp, div_le_iff₀ hmreal, one_mul]
    exact (Real.log_le_log hx hxM).trans hmlo
  let q : GLₙ := diagonalPower a ha (1 / (m : ℝ))
  have hq : unitHeight q ≤ Real.exp 1 :=
    diagonalPower_height_le F n a ha _ _ (Real.one_le_exp (by norm_num))
      (fun i => hsmall _ (ha i) (hai i)) (fun i => hsmall _ (inv_pos.mpr (ha i)) (hainv i))
  refine ⟨k, q, l, m, hK _ hk, hK _ hl, hq, hm, hmhi, ?_⟩
  rw [show q ^ m = d from diagonalPower_root_pow F n a ha m hm.ne']
  exact hfac

private theorem nat_pow_bound_of_log_le {B M : ℝ} {m : ℕ} (hB : 1 ≤ B) (hM : 1 ≤ M)
    (hm : (m : ℝ) ≤ Real.log M + 2) : B ^ m ≤ B ^ 2 * M ^ ⌈Real.log B⌉₊ := by
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hlogB := Real.log_nonneg hB
  have hlogM := Real.log_nonneg hM
  calc
    B ^ m = Real.exp ((m : ℝ) * Real.log B) := by rw [Real.exp_nat_mul, Real.exp_log hBpos]
    _ ≤ Real.exp ((Real.log M + 2) * Real.log B) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hm hlogB)
    _ = B ^ 2 * Real.exp (Real.log B * Real.log M) := by
      have he : (Real.log M + 2) * Real.log B =
          (↑(2 : ℕ) : ℝ) * Real.log B + Real.log B * Real.log M := by push_cast; ring
      rw [he, Real.exp_add, Real.exp_nat_mul, Real.exp_log hBpos]
    _ ≤ B ^ 2 * Real.exp ((⌈Real.log B⌉₊ : ℝ) * Real.log M) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (Nat.le_ceil _) hlogM)) (by positivity)
    _ = B ^ 2 * M ^ ⌈Real.log B⌉₊ := by
      rw [Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans_le hM)]

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (R : Langlands.GeneralLinear n F →* (E →L[ℂ] E))

private theorem norm_bound_on_compact (hR : IsContinuousRepresentation R)
    {s : Set GLₙ} (hs : IsCompact s) : ∃ B : ℝ, 1 ≤ B ∧ ∀ g ∈ s, ‖R g‖ ≤ B := by
  let ops : s → E →L[ℂ] E := fun g => R g.1
  have hp (v : E) : ∃ b : ℝ, ∀ g : s, ‖ops g v‖ ≤ b := by
    have hv : Continuous (fun g : GLₙ => R g v) :=
      hR.comp (continuous_id.prodMk continuous_const)
    obtain ⟨b, hb⟩ := hs.exists_bound_of_continuousOn hv.continuousOn
    exact ⟨b, fun g => hb g.1 g.2⟩
  obtain ⟨B, hB⟩ := banach_steinhaus (g := ops) hp
  exact ⟨max 1 B, le_max_left _ _, fun g hg => (hB ⟨g, hg⟩).trans (le_max_right _ _)⟩

/-- Any jointly continuous complex Banach representation of actual real or complex general
linear matrices has an operator bound polynomial in the unit height. -/
theorem exists_norm_le_unitHeight_pow (hR : IsContinuousRepresentation R) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ g : GLₙ, ‖R g‖ ≤ C * unitHeight (A := Mat) g ^ d := by
  have hC₀' : ∃ C₀ : ℝ, ∀ k ∈ unitaryCompact F n, ‖unitHeight (A := Mat) k‖ ≤ C₀ :=
    (isCompact_unitaryCompact F n).exists_bound_of_continuousOn
      (continuous_unitHeight (A := Mat)).continuousOn
  obtain ⟨C₀, hC₀⟩ := hC₀'
  let C := max 1 C₀
  have hC : 1 ≤ C := le_max_left _ _
  have hK (k : GLₙ) (hk : k ∈ unitaryCompact F n) : unitHeight k ≤ C :=
    ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC₀ k hk)).trans
      (le_max_right _ _)
  have hs : IsCompact {g : GLₙ | unitHeight g ≤ max C (Real.exp 1)} :=
    isCompact_unitHeight_sublevel (hC.trans (le_max_left _ _))
  obtain ⟨B, hB, hbound⟩ := norm_bound_on_compact F n R hR hs
  let d := ⌈Real.log B⌉₊
  refine ⟨B ^ 4 * (C ^ 2) ^ d, d, by positivity, fun g => ?_⟩
  obtain ⟨k, q, l, m, hk, hl, hq, hm, hmhi, hfac⟩ := exists_bounded_root_factors F n C hC hK g
  let M := C ^ 2 * unitHeight g
  have hM : 1 ≤ M := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) (one_le_unitHeight g)
  have hpow : B ^ m ≤ B ^ 2 * M ^ d := nat_pow_bound_of_log_le hB hM hmhi
  have hkB := hbound k (hk.trans (le_max_left _ _))
  have hqB := hbound q (hq.trans (le_max_right _ _))
  have hlB := hbound l (hl.trans (le_max_left _ _))
  calc
    ‖R g‖ = ‖R k * R q ^ m * R l‖ := by rw [hfac, map_mul, map_mul, map_pow]
    _ ≤ (‖R k‖ * ‖R q‖ ^ m) * ‖R l‖ := by
      refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_pow_le' _ hm) (norm_nonneg _))
    _ ≤ (B * B ^ m) * B := by gcongr
    _ ≤ (B * (B ^ 2 * M ^ d)) * B := by gcongr
    _ = (B ^ 4 * (C ^ 2) ^ d) * unitHeight g ^ d := by unfold M; rw [mul_pow]; ring

end GeneralLinear

end Langlands.Archimedean
