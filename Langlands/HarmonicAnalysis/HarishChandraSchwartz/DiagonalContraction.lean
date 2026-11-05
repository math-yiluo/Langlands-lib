import Langlands.GroupScheme.Dynamic.GeneralLinear
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Height
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ContractionScaling

/-! # Contraction of block unipotent matrices by diagonal conjugation

Matrix lemmas for the contraction-scaling proof of Waldspurger 2003, II.2 (6). Over a normed
field `F`, conjugation `g ↦ D⁻¹ g D` by `D = diag(t ^ e i)` with `‖t‖ ≤ 1` shrinks the entries
of `g - 1` for `g` block unipotent for the weights `-e` by at least the factor `‖t‖`, and by at
most `‖t‖ ^ d` when `d` bounds the weight gaps. For a vector `w` supported on the weight block
`{e = m}`, it also shrinks `g w - w` by at least `‖t‖` in the sup norm. Combined with
`exists_le_mul_pow_of_contractionScaling`, this gives an inverse power bound for the entries
of `g - 1` in terms of `‖g w - w‖`.
-/

noncomputable section

open Matrix
open Langlands.GroupScheme.GeneralLinear

namespace Langlands.HarishChandraSchwartz

section DiagonalContraction

variable {F : Type*} [NormedField F] {n : Type} [Fintype n] [DecidableEq n] (e : n → ℤ)

/-- The largest absolute value of an entry of `g - 1`. -/
def offIdentityNorm [Nonempty n] (g : GL n F) : ℝ :=
  entryNorm ((g : Matrix n n F) - 1)

theorem offIdentityNorm_nonneg [Nonempty n] (g : GL n F) : 0 ≤ offIdentityNorm g :=
  entryNorm_nonneg _

@[simp] theorem offIdentityNorm_one [Nonempty n] : offIdentityNorm (1 : GL n F) = 0 := by
  refine le_antisymm (entryNorm_le fun i j => ?_) (entryNorm_nonneg _)
  simp

/-- The entries of `D⁻¹ g D` for `D = diag(t ^ e i)`. -/
theorem diagonalUnits_conj_apply (t : Fˣ) (g : GL n F) (i j : n) :
    (((diagonalUnits F e t)⁻¹ * g * diagonalUnits F e t : GL n F) : Matrix n n F) i j =
      (t : F) ^ (e j - e i) * (g : Matrix n n F) i j := by
  have ht : (t : F) ≠ 0 := t.ne_zero
  rw [← map_inv, Units.val_mul, Units.val_mul, coe_diagonalUnits, coe_diagonalUnits,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Units.val_zpow_eq_zpow_val,
    Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, inv_zpow', zpow_sub₀ ht,
    zpow_neg]
  field_simp

/-- Diagonal conjugation preserves block unipotence for the weights `-e`. -/
theorem diagonalUnits_conj_mem (t : Fˣ) {g : GL n F}
    (hg : g ∈ blockUnipotentSubgroup F (-e)) :
    (diagonalUnits F e t)⁻¹ * g * diagonalUnits F e t ∈ blockUnipotentSubgroup F (-e) := by
  intro i j hij
  rw [diagonalUnits_conj_apply, hg i j hij]
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

omit [DecidableEq n] in
/-- Finitely many weights have bounded gaps. -/
theorem exists_weight_gap_le : ∃ d : ℕ, ∀ i j, e i < e j → e j - e i ≤ d := by
  refine ⟨Finset.univ.sup fun p : n × n => (e p.2 - e p.1).toNat, fun i j _ => ?_⟩
  have h : (e j - e i).toNat ≤ Finset.univ.sup fun p : n × n => (e p.2 - e p.1).toNat :=
    Finset.le_sup (f := fun p : n × n => (e p.2 - e p.1).toNat) (Finset.mem_univ (i, j))
  calc e j - e i ≤ ((e j - e i).toNat : ℤ) := Int.self_le_toNat _
    _ ≤ _ := by exact_mod_cast h

/-- **One-step contraction.** For `g` block unipotent for `-e` and `‖t‖ ≤ 1`, the entries of
`D⁻¹ g D - 1` are at most `‖t‖` times the largest entry of `g - 1`. -/
theorem offIdentityNorm_conj_le [Nonempty n] (t : Fˣ) (ht : ‖(t : F)‖ ≤ 1) {g : GL n F}
    (hg : g ∈ blockUnipotentSubgroup F (-e)) :
    offIdentityNorm ((diagonalUnits F e t)⁻¹ * g * diagonalUnits F e t) ≤
      ‖(t : F)‖ * offIdentityNorm g := by
  have hpos : 0 < ‖(t : F)‖ := norm_pos_iff.2 t.ne_zero
  have hR : 0 ≤ ‖(t : F)‖ * offIdentityNorm g :=
    mul_nonneg (norm_nonneg _) (offIdentityNorm_nonneg g)
  refine entryNorm_le fun i j => ?_
  rw [Matrix.sub_apply, diagonalUnits_conj_apply]
  by_cases hij : e j ≤ e i
  · rw [hg i j (by simpa using hij)]
    by_cases h : i = j
    · subst h
      simpa using hR
    · simpa [Matrix.one_apply_ne h] using hR
  · rw [not_le] at hij
    have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
    rw [Matrix.one_apply_ne hne, sub_zero, norm_mul, norm_zpow]
    have hk : ‖(t : F)‖ ^ (e j - e i) ≤ ‖(t : F)‖ := by
      simpa using zpow_le_zpow_right_of_le_one₀ hpos ht (show (1 : ℤ) ≤ e j - e i by omega)
    have hg' : ‖(g : Matrix n n F) i j‖ ≤ offIdentityNorm g := by
      have := norm_le_entryNorm ((g : Matrix n n F) - 1) i j
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at this
    exact mul_le_mul hk hg' (norm_nonneg _) (norm_nonneg _)

/-- **Bounded expansion.** If every weight gap is at most `d`, the entries of `g - 1` are at
most `‖t‖⁻¹ ^ d` times the largest entry of `D⁻¹ g D - 1`. -/
theorem offIdentityNorm_le_conj [Nonempty n] (t : Fˣ) (ht : ‖(t : F)‖ ≤ 1) {d : ℕ}
    (hd : ∀ i j, e i < e j → e j - e i ≤ d) {g : GL n F}
    (hg : g ∈ blockUnipotentSubgroup F (-e)) :
    offIdentityNorm g ≤
      ‖(t : F)‖⁻¹ ^ d * offIdentityNorm ((diagonalUnits F e t)⁻¹ * g * diagonalUnits F e t) := by
  have hpos : 0 < ‖(t : F)‖ := norm_pos_iff.2 t.ne_zero
  have hR : 0 ≤ ‖(t : F)‖⁻¹ ^ d *
      offIdentityNorm ((diagonalUnits F e t)⁻¹ * g * diagonalUnits F e t) :=
    mul_nonneg (pow_nonneg (inv_nonneg.2 (norm_nonneg _)) d) (offIdentityNorm_nonneg _)
  refine entryNorm_le fun i j => ?_
  by_cases hij : e j ≤ e i
  · rw [Matrix.sub_apply, hg i j (by simpa using hij), sub_self, norm_zero]
    exact hR
  · rw [not_le] at hij
    have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
    have hc := norm_le_entryNorm
      (((diagonalUnits F e t)⁻¹ * g * diagonalUnits F e t : GL n F) - 1 : Matrix n n F) i j
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero, diagonalUnits_conj_apply,
      norm_mul, norm_zpow] at hc
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
    have hk : ‖(t : F)‖⁻¹ ^ (e j - e i) ≤ ‖(t : F)‖⁻¹ ^ (d : ℤ) :=
      zpow_le_zpow_right₀ (one_le_inv₀ hpos |>.2 ht) (hd i j hij)
    have hk0 : 0 ≤ ‖(t : F)‖⁻¹ ^ (e j - e i) := zpow_nonneg (inv_nonneg.2 hpos.le) _
    have hone : ‖(t : F)‖⁻¹ ^ (e j - e i) * ‖(t : F)‖ ^ (e j - e i) = 1 := by
      rw [inv_zpow, inv_mul_cancel₀ (zpow_ne_zero _ hpos.ne')]
    calc ‖(g : Matrix n n F) i j‖
        = ‖(t : F)‖⁻¹ ^ (e j - e i) * (‖(t : F)‖ ^ (e j - e i) * ‖(g : Matrix n n F) i j‖) := by
          rw [← mul_assoc, hone, one_mul]
      _ ≤ ‖(t : F)‖⁻¹ ^ (e j - e i) *
            offIdentityNorm ((diagonalUnits F e t)⁻¹ * g * diagonalUnits F e t) :=
          mul_le_mul_of_nonneg_left hc hk0
      _ ≤ ‖(t : F)‖⁻¹ ^ (d : ℤ) *
            offIdentityNorm ((diagonalUnits F e t)⁻¹ * g * diagonalUnits F e t) :=
          mul_le_mul_of_nonneg_right hk (offIdentityNorm_nonneg _)
      _ = _ := by rw [zpow_natCast]

variable {e}

/-- For `g` block unipotent for `-e` and `w` supported on `{e = m}`, the vector `g w - w` has
zero components at all indices of weight at least `m`. -/
theorem mulVec_sub_apply_eq_zero {g : GL n F} (hg : g ∈ blockUnipotentSubgroup F (-e))
    {m : ℤ} {w : n → F} (hw : ∀ k, e k ≠ m → w k = 0) {i : n} (hi : m ≤ e i) :
    ((g : Matrix n n F) *ᵥ w - w) i = 0 := by
  have h : ∀ k, (g : Matrix n n F) i k * w k = (1 : Matrix n n F) i k * w k := by
    intro k
    by_cases hk : e k = m
    · rw [hg i k (by simp only [Pi.neg_apply, neg_le_neg_iff]; omega)]
    · rw [hw k hk, mul_zero, mul_zero]
  rw [Pi.sub_apply, sub_eq_zero]
  calc ((g : Matrix n n F) *ᵥ w) i = ∑ k, (g : Matrix n n F) i k * w k := rfl
    _ = ∑ k, (1 : Matrix n n F) i k * w k := Finset.sum_congr rfl fun k _ => h k
    _ = ((1 : Matrix n n F) *ᵥ w) i := rfl
    _ = w i := by rw [Matrix.one_mulVec]

/-- For `w` supported on `{e = m}`, the `i`-th component of `D⁻¹ g D w - w` is
`t ^ (m - e i)` times that of `g w - w`. -/
theorem conj_mulVec_sub_apply (t : Fˣ) (g : GL n F) {m : ℤ} {w : n → F}
    (hw : ∀ k, e k ≠ m → w k = 0) (i : n) :
    ((((diagonalUnits F e t)⁻¹ * g * diagonalUnits F e t : GL n F) : Matrix n n F) *ᵥ w - w) i =
      (t : F) ^ (m - e i) * (((g : Matrix n n F) *ᵥ w - w) i) := by
  have h1 : ∀ k, (t : F) ^ (e k - e i) * (g : Matrix n n F) i k * w k =
      (t : F) ^ (m - e i) * ((g : Matrix n n F) i k * w k) := by
    intro k
    by_cases hk : e k = m
    · rw [hk, mul_assoc]
    · rw [hw k hk, mul_zero, mul_zero, mul_zero]
  have h2 : w i = (t : F) ^ (m - e i) * w i := by
    by_cases hi : e i = m
    · rw [hi, sub_self, zpow_zero, one_mul]
    · rw [hw i hi, mul_zero]
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, diagonalUnits_conj_apply]
  rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.mul_sum, mul_sub, ← h2]

/-- **One-step contraction of `g w - w`.** For `g` block unipotent for `-e`, `w` supported on
`{e = m}` and `‖t‖ ≤ 1`, the sup norm of `D⁻¹ g D w - w` is at most `‖t‖` times that of
`g w - w`. -/
theorem norm_conj_mulVec_sub_le (t : Fˣ) (ht : ‖(t : F)‖ ≤ 1) {g : GL n F}
    (hg : g ∈ blockUnipotentSubgroup F (-e)) {m : ℤ} {w : n → F}
    (hw : ∀ k, e k ≠ m → w k = 0) :
    ‖(((diagonalUnits F e t)⁻¹ * g * diagonalUnits F e t : GL n F) : Matrix n n F) *ᵥ w - w‖ ≤
      ‖(t : F)‖ * ‖(g : Matrix n n F) *ᵥ w - w‖ := by
  have hpos : 0 < ‖(t : F)‖ := norm_pos_iff.2 t.ne_zero
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 fun i => ?_
  rw [conj_mulVec_sub_apply t g hw i]
  by_cases hi : m ≤ e i
  · rw [mulVec_sub_apply_eq_zero hg hw hi, mul_zero, norm_zero]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · rw [not_le] at hi
    rw [norm_mul, norm_zpow]
    have hk : ‖(t : F)‖ ^ (m - e i) ≤ ‖(t : F)‖ := by
      simpa using zpow_le_zpow_right_of_le_one₀ hpos ht (show (1 : ℤ) ≤ m - e i by omega)
    exact mul_le_mul hk (norm_le_pi_norm _ i) (norm_nonneg _) (norm_nonneg _)

/-- **Inverse power bound for block unipotent matrix families.** Let `c : X → X` and
`r₀ : X → GL n F`, `r : X → GL n' F` with values block unipotent for `-e₀` and `-e`, such that
`c` acts by conjugation with `diag(t ^ e₀ i)` and `diag(t ^ e i)`, where `‖t‖ < 1`. Let `w` be
supported on `{e = m}`, assume `r x w = w` only if `r₀ x = 1`, and let `d` bound the gaps of
`e₀`. If the annulus `{1 ≤ ‖t‖⁻¹ ^ d β, β ≤ 1}` for `β x = offIdentityNorm (r₀ x)` is compact
and `x ↦ ‖r x w - w‖` is continuous on it, then `β x ≤ C ‖r x w - w‖ ^ d` whenever
`1 ≤ β x`, for some `C > 0`. -/
theorem exists_offIdentityNorm_le_mul_pow [Nonempty n] {n' : Type} [Fintype n'] [DecidableEq n']
    {X : Type*} [TopologicalSpace X] (c : X → X) (r₀ : X → GL n F) (r : X → GL n' F)
    {e₀ : n → ℤ} {e : n' → ℤ} (t : Fˣ) (ht : ‖(t : F)‖ < 1)
    (hr₀ : ∀ x, r₀ x ∈ blockUnipotentSubgroup F (-e₀))
    (hr : ∀ x, r x ∈ blockUnipotentSubgroup F (-e))
    (hr₀c : ∀ x, r₀ (c x) = (diagonalUnits F e₀ t)⁻¹ * r₀ x * diagonalUnits F e₀ t)
    (hrc : ∀ x, r (c x) = (diagonalUnits F e t)⁻¹ * r x * diagonalUnits F e t)
    {m : ℤ} {w : n' → F} (hw : ∀ k, e k ≠ m → w k = 0)
    (hfix : ∀ x, (r x : Matrix n' n' F) *ᵥ w = w → r₀ x = 1)
    {d : ℕ} (hd : ∀ i j, e₀ i < e₀ j → e₀ j - e₀ i ≤ d)
    (hS : IsCompact (contractionScalingAnnulus (fun x => offIdentityNorm (r₀ x)) ‖(t : F)‖⁻¹ d))
    (hcont : ContinuousOn (fun x => ‖(r x : Matrix n' n' F) *ᵥ w - w‖)
      (contractionScalingAnnulus (fun x => offIdentityNorm (r₀ x)) ‖(t : F)‖⁻¹ d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, 1 ≤ offIdentityNorm (r₀ x) →
      offIdentityNorm (r₀ x) ≤ C * ‖(r x : Matrix n' n' F) *ᵥ w - w‖ ^ d := by
  have hpos : 0 < ‖(t : F)‖ := norm_pos_iff.2 t.ne_zero
  have hq1 : 1 ≤ ‖(t : F)‖⁻¹ := one_le_inv₀ hpos |>.2 ht.le
  have hcontr : ∀ x, offIdentityNorm (r₀ (c x)) ≤ ‖(t : F)‖ * offIdentityNorm (r₀ x) := by
    intro x
    rw [hr₀c]
    exact offIdentityNorm_conj_le e₀ t ht.le (hr₀ x)
  refine exists_le_mul_pow_of_contractionScaling hq1 (fun x => ?_) (fun x => ?_)
    (exists_iterate_le_one_of_le_mul (c := c) (β := fun x => offIdentityNorm (r₀ x))
      (norm_nonneg _) ht hcontr) hS hcont (fun x hx => ?_)
  · rw [hr₀c]
    exact offIdentityNorm_le_conj e₀ t ht.le hd (hr₀ x)
  · have h := norm_conj_mulVec_sub_le t ht.le (hr x) hw
    rw [← hrc] at h
    calc ‖(t : F)‖⁻¹ * ‖(r (c x) : Matrix n' n' F) *ᵥ w - w‖
        ≤ ‖(t : F)‖⁻¹ * (‖(t : F)‖ * ‖(r x : Matrix n' n' F) *ᵥ w - w‖) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.2 hpos.le)
      _ = ‖(r x : Matrix n' n' F) *ᵥ w - w‖ := by
          rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  · refine (norm_nonneg _).lt_of_ne fun h0 => ?_
    have h1 : r₀ x = 1 := hfix x (sub_eq_zero.1 (norm_eq_zero.1 h0.symm))
    have h2 := hx.1
    simp only [h1, offIdentityNorm_one, mul_zero] at h2
    exact absurd h2 (by norm_num)

end DiagonalContraction

end Langlands.HarishChandraSchwartz
