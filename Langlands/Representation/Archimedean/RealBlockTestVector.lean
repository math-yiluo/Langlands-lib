import Langlands.Representation.Archimedean.RealInductionStagesFourier
import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Langlands.Representation.Archimedean.JacquetKernel

/-!
# Polynomial test vectors on `O(n)` for real standard modules

Explicit functions on `O(n)` built from the entries of the rows of a block `b, b + 1`:
`Z_c = κ_{b,c} + i κ_{b+1,c}` and its conjugate `Z̄_c`, and the block factor
`Z_c^m Z_{c'} + Z̄_c^m Z̄_{c'}`, which has exactly the two Fourier modes `±(m + 1)` under the
left rotations of the block `b`. A continuous `O(n)`-finite function on matrices transforming
under the diagonal sign matrices like the position characters of a list `ds` and whose block
Fourier coefficients of small weight vanish at the induction blocks of `ds` is the restriction
to `O(n)` of an `O(n)`-finite function of the standard module of `ds` (`exists_KF`).
-/

noncomputable section

open scoped Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

set_option backward.isDefEq.respectTransparency false

namespace RealBlockTestVector

open Langlands.LocalFactor.Archimedean
open RealBlockRotation RealBlockFourierFinite

variable {n : ℕ}

section TestVector

open TranslateFinite PrincipalSeriesExtension GramFormula

/-! ### Entries of rotated matrices -/

variable {b : ℕ}

theorem rot_mul_ia (hb : b + 1 < n) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) (c : Fin n) :
    ((blockRotation n b φ : Matrix (Fin n) (Fin n) ℝ) * κ) (ia hb) c =
      Real.cos φ * κ (ia hb) c - Real.sin φ * κ (ib hb) c := by
  rw [blockRotation_val_eq hb, rotMatrix_mul_apply hb, blockProj, rotationGenerator_eq hb]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.add_apply, Matrix.sub_apply,
    Matrix.single_mul_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ (ia_ne_ib hb),
    one_mul]
  ring

theorem rot_mul_ib (hb : b + 1 < n) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) (c : Fin n) :
    ((blockRotation n b φ : Matrix (Fin n) (Fin n) ℝ) * κ) (ib hb) c =
      Real.sin φ * κ (ia hb) c + Real.cos φ * κ (ib hb) c := by
  rw [blockRotation_val_eq hb, rotMatrix_mul_apply hb, blockProj, rotationGenerator_eq hb]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.add_apply, Matrix.sub_apply,
    Matrix.single_mul_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ (ia_ne_ib hb).symm,
    one_mul]
  ring

theorem rot_mul_of_ne (hb : b + 1 < n) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) {i : Fin n}
    (h1 : i ≠ ia hb) (h2 : i ≠ ib hb) (c : Fin n) :
    ((blockRotation n b φ : Matrix (Fin n) (Fin n) ℝ) * κ) i c = κ i c := by
  rw [blockRotation_val_eq hb, rotMatrix_mul_apply hb, blockProj, rotationGenerator_eq hb]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.add_apply, Matrix.sub_apply,
    Matrix.single_mul_apply_of_ne _ _ _ _ _ h1, Matrix.single_mul_apply_of_ne _ _ _ _ _ h2]
  ring

/-! ### The complex coordinates of a block -/

/-- `Z_c(κ) = κ_{b,c} + i κ_{b+1,c}`: the entries of column `c` in the rows of the block `b`,
as a complex number. -/
def zp (hb : b + 1 < n) (c : Fin n) (κ : Matrix (Fin n) (Fin n) ℝ) : ℂ :=
  (κ (ia hb) c : ℂ) + Complex.I * (κ (ib hb) c : ℂ)

/-- The conjugate `Z̄_c(κ) = κ_{b,c} - i κ_{b+1,c}`. -/
def zm (hb : b + 1 < n) (c : Fin n) (κ : Matrix (Fin n) (Fin n) ℝ) : ℂ :=
  (κ (ia hb) c : ℂ) - Complex.I * (κ (ib hb) c : ℂ)

theorem expMode_one_eq (φ : ℝ) : expMode 1 φ = Real.cos φ + Complex.I * Real.sin φ := by
  have h : ((1 : ℤ) : ℂ) * (φ : ℂ) * Complex.I = (φ : ℂ) * Complex.I := by push_cast; ring
  rw [expMode, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

theorem expMode_neg_one_eq (φ : ℝ) :
    expMode (-1) φ = Real.cos φ - Complex.I * Real.sin φ := by
  have h : ((-1 : ℤ) : ℂ) * (φ : ℂ) * Complex.I = ((-φ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [expMode, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast
  ring

theorem zp_rot (hb : b + 1 < n) (c : Fin n) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    zp hb c ((blockRotation n b φ : Matrix (Fin n) (Fin n) ℝ) * κ) =
      expMode 1 φ * zp hb c κ := by
  rw [zp, zp, rot_mul_ia, rot_mul_ib, expMode_one_eq]
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
  linear_combination (-(Real.sin φ : ℂ) * (κ (ib hb) c : ℂ)) * Complex.I_sq

theorem zm_rot (hb : b + 1 < n) (c : Fin n) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    zm hb c ((blockRotation n b φ : Matrix (Fin n) (Fin n) ℝ) * κ) =
      expMode (-1) φ * zm hb c κ := by
  rw [zm, zm, rot_mul_ia, rot_mul_ib, expMode_neg_one_eq]
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]
  linear_combination (-(Real.sin φ : ℂ) * (κ (ib hb) c : ℂ)) * Complex.I_sq

/-- The block factor `Z_c^m Z_{c'} + Z̄_c^m Z̄_{c'}` of degree `m + 1` at the block `b`. -/
def bf (hb : b + 1 < n) (c c' : Fin n) (m : ℕ) (κ : Matrix (Fin n) (Fin n) ℝ) : ℂ :=
  zp hb c κ ^ m * zp hb c' κ + zm hb c κ ^ m * zm hb c' κ

theorem expMode_pow_mul (k : ℤ) (m : ℕ) (φ : ℝ) :
    expMode k φ ^ m * expMode k φ = expMode (((m : ℤ) + 1) * k) φ := by
  simp only [expMode, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Under the rotations of its block, the block factor has the two modes `±(m + 1)`. -/
theorem bf_rot (hb : b + 1 < n) (c c' : Fin n) (m : ℕ) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    bf hb c c' m ((blockRotation n b φ : Matrix (Fin n) (Fin n) ℝ) * κ) =
      expMode ((m : ℤ) + 1) φ * (zp hb c κ ^ m * zp hb c' κ) +
        expMode (-((m : ℤ) + 1)) φ * (zm hb c κ ^ m * zm hb c' κ) := by
  have h1 := expMode_pow_mul 1 m φ
  have h2 := expMode_pow_mul (-1) m φ
  rw [mul_one] at h1
  rw [mul_neg_one] at h2
  rw [bf, zp_rot, zp_rot, zm_rot, zm_rot, mul_pow, mul_pow, ← h1, ← h2]
  ring

/-- Rows outside the block `b'` are not moved by the rotations of `b'`. -/
theorem zp_rot_of_disjoint (hb : b + 1 < n) {b' : ℕ} (hb' : b' + 1 < n)
    (hd : b + 1 < b' ∨ b' + 1 < b) (c : Fin n) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    zp hb c ((blockRotation n b' φ : Matrix (Fin n) (Fin n) ℝ) * κ) = zp hb c κ := by
  have h1 : ia hb ≠ ia hb' := fun h => by simp [ia, Fin.ext_iff] at h; omega
  have h2 : ia hb ≠ ib hb' := fun h => by simp [ia, ib, Fin.ext_iff] at h; omega
  have h3 : ib hb ≠ ia hb' := fun h => by simp [ia, ib, Fin.ext_iff] at h; omega
  have h4 : ib hb ≠ ib hb' := fun h => by simp [ib, Fin.ext_iff] at h; omega
  rw [zp, zp, rot_mul_of_ne hb' φ κ h1 h2, rot_mul_of_ne hb' φ κ h3 h4]

theorem zm_rot_of_disjoint (hb : b + 1 < n) {b' : ℕ} (hb' : b' + 1 < n)
    (hd : b + 1 < b' ∨ b' + 1 < b) (c : Fin n) (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    zm hb c ((blockRotation n b' φ : Matrix (Fin n) (Fin n) ℝ) * κ) = zm hb c κ := by
  have h1 : ia hb ≠ ia hb' := fun h => by simp [ia, Fin.ext_iff] at h; omega
  have h2 : ia hb ≠ ib hb' := fun h => by simp [ia, ib, Fin.ext_iff] at h; omega
  have h3 : ib hb ≠ ia hb' := fun h => by simp [ia, ib, Fin.ext_iff] at h; omega
  have h4 : ib hb ≠ ib hb' := fun h => by simp [ib, Fin.ext_iff] at h; omega
  rw [zm, zm, rot_mul_of_ne hb' φ κ h1 h2, rot_mul_of_ne hb' φ κ h3 h4]

theorem bf_rot_of_disjoint (hb : b + 1 < n) {b' : ℕ} (hb' : b' + 1 < n)
    (hd : b + 1 < b' ∨ b' + 1 < b) (c c' : Fin n) (m : ℕ) (φ : ℝ)
    (κ : Matrix (Fin n) (Fin n) ℝ) :
    bf hb c c' m ((blockRotation n b' φ : Matrix (Fin n) (Fin n) ℝ) * κ) = bf hb c c' m κ := by
  rw [bf, bf, zp_rot_of_disjoint hb hb' hd, zp_rot_of_disjoint hb hb' hd,
    zm_rot_of_disjoint hb hb' hd, zm_rot_of_disjoint hb hb' hd]

/-! ### Two modes -/

/-- The Fourier coefficients of `e^{iNφ} A + e^{-iNφ} B`. -/
theorem coeff_two_mode (N : ℤ) (A B : ℂ) (j : ℤ) :
    coeff j (fun φ => expMode N φ * A + expMode (-N) φ * B) =
      (if N = j then 2 * (Real.pi : ℂ) * A else 0) +
        (if -N = j then 2 * (Real.pi : ℂ) * B else 0) := by
  have h : (fun φ => expMode N φ * A + expMode (-N) φ * B) = A • expMode N + B • expMode (-N) := by
    funext φ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, coeff_add ((continuous_expMode N).const_smul A) ((continuous_expMode _).const_smul B),
    coeff_smul, coeff_smul, coeff_expMode, coeff_expMode]
  split_ifs <;> ring

theorem coeff_two_mode_eq_zero {N : ℤ} (A B : ℂ) {j : ℤ} (hj : |j| < |N|) :
    coeff j (fun φ => expMode N φ * A + expMode (-N) φ * B) = 0 := by
  have h1 : N ≠ j := fun h => by rw [h] at hj; exact lt_irrefl _ hj
  have h2 : -N ≠ j := fun h => by rw [← h, abs_neg] at hj; exact lt_irrefl _ hj
  rw [coeff_two_mode]
  simp only [h1, h2, ↓reduceIte, add_zero]

/-! ### Signs -/

/-- `F(diag(s) κ) = (∏ s_i^{q_i}) F(κ)` for all sign vectors `s`. -/
def IsSignEq (q : Fin n → ℕ) (F : Matrix (Fin n) (Fin n) ℝ → ℂ) : Prop :=
  ∀ s : Fin n → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ∀ κ : Matrix (Fin n) (Fin n) ℝ,
    F (Matrix.diagonal s * κ) = (∏ i, ((s i : ℝ) : ℂ) ^ q i) * F κ

theorem isSignEq_mul {q q' : Fin n → ℕ} {F G : Matrix (Fin n) (Fin n) ℝ → ℂ}
    (hF : IsSignEq q F) (hG : IsSignEq q' G) : IsSignEq (q + q') (fun κ => F κ * G κ) := by
  intro s hs κ
  dsimp only
  rw [hF s hs κ, hG s hs κ]
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  ring

theorem isSignEq_pow {q : Fin n → ℕ} {F : Matrix (Fin n) (Fin n) ℝ → ℂ}
    (hF : IsSignEq q F) (m : ℕ) : IsSignEq (m • q) (fun κ => F κ ^ m) := by
  intro s hs κ
  dsimp only
  rw [hF s hs κ, mul_pow, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, pow_mul]

theorem prod_pow_single (s : Fin n → ℝ) (i : Fin n) (m : ℕ) :
    ∏ j, ((s j : ℝ) : ℂ) ^ (Pi.single i m : Fin n → ℕ) j = ((s i : ℝ) : ℂ) ^ m := by
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem isSignEq_entry (i c : Fin n) :
    IsSignEq (Pi.single i 1) (fun κ => ((κ i c : ℝ) : ℂ)) := by
  intro s _ κ
  dsimp only
  rw [prod_pow_single, Matrix.diagonal_mul]
  push_cast
  ring

theorem zp_diag (hb : b + 1 < n) (c : Fin n) (s : Fin n → ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    zp hb c (Matrix.diagonal s * κ) =
      (s (ia hb) : ℂ) * κ (ia hb) c + Complex.I * ((s (ib hb) : ℂ) * κ (ib hb) c) := by
  rw [zp, Matrix.diagonal_mul, Matrix.diagonal_mul]
  push_cast
  ring

theorem zm_diag (hb : b + 1 < n) (c : Fin n) (s : Fin n → ℝ) (κ : Matrix (Fin n) (Fin n) ℝ) :
    zm hb c (Matrix.diagonal s * κ) =
      (s (ia hb) : ℂ) * κ (ia hb) c - Complex.I * ((s (ib hb) : ℂ) * κ (ib hb) c) := by
  rw [zm, Matrix.diagonal_mul, Matrix.diagonal_mul]
  push_cast
  ring

/-- The block factor of degree `m + 1` transforms by `s_b^{m + 1}`. -/
theorem isSignEq_bf (hb : b + 1 < n) (c c' : Fin n) (m : ℕ) :
    IsSignEq (Pi.single (ia hb) (m + 1)) (bf hb c c' m) := by
  intro s hs κ
  rw [prod_pow_single, bf, bf, zp_diag, zp_diag, zm_diag, zm_diag]
  rcases hs (ia hb) with h1 | h1 <;> rcases hs (ib hb) with h2 | h2 <;> rw [h1, h2] <;>
    push_cast
  · simp only [one_mul, one_pow, zp, zm]
  · simp only [one_mul, one_pow, zp, zm]
    ring
  · have e1 : (-1 * (κ (ia hb) c : ℂ) + Complex.I * (1 * (κ (ib hb) c : ℂ))) = -zm hb c κ := by
      rw [zm]; ring
    have e2 : (-1 * (κ (ia hb) c : ℂ) - Complex.I * (1 * (κ (ib hb) c : ℂ))) = -zp hb c κ := by
      rw [zp]; ring
    have e3 : (-1 * (κ (ia hb) c' : ℂ) + Complex.I * (1 * (κ (ib hb) c' : ℂ))) = -zm hb c' κ := by
      rw [zm]; ring
    have e4 : (-1 * (κ (ia hb) c' : ℂ) - Complex.I * (1 * (κ (ib hb) c' : ℂ))) = -zp hb c' κ := by
      rw [zp]; ring
    rw [e1, e2, e3, e4, neg_pow, neg_pow (zp hb c κ), pow_succ]
    ring
  · have e1 : (-1 * (κ (ia hb) c : ℂ) + Complex.I * (-1 * (κ (ib hb) c : ℂ))) = -zp hb c κ := by
      rw [zp]; ring
    have e2 : (-1 * (κ (ia hb) c : ℂ) - Complex.I * (-1 * (κ (ib hb) c : ℂ))) = -zm hb c κ := by
      rw [zm]; ring
    have e3 : (-1 * (κ (ia hb) c' : ℂ) + Complex.I * (-1 * (κ (ib hb) c' : ℂ))) =
        -zp hb c' κ := by
      rw [zp]; ring
    have e4 : (-1 * (κ (ia hb) c' : ℂ) - Complex.I * (-1 * (κ (ib hb) c' : ℂ))) =
        -zm hb c' κ := by
      rw [zm]; ring
    rw [e1, e2, e3, e4, neg_pow, neg_pow (zm hb c κ), pow_succ]
    ring

/-! ### Translate-finiteness and continuity -/

theorem isTranslateFinite_zp (hb : b + 1 < n) (c : Fin n) :
    IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => zp hb c (κ : Matrix (Fin n) (Fin n) ℝ)) :=
  isTranslateFinite_add (isTranslateFinite_entry (ia hb, c))
    (isTranslateFinite_smul (isTranslateFinite_entry (ib hb, c)) Complex.I)

theorem isTranslateFinite_zm (hb : b + 1 < n) (c : Fin n) :
    IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => zm hb c (κ : Matrix (Fin n) (Fin n) ℝ)) := by
  have h := isTranslateFinite_add (isTranslateFinite_entry (ia hb, c))
    (isTranslateFinite_smul (isTranslateFinite_entry (ib hb, c)) (-Complex.I))
  have e : (fun κ : Matrix.unitaryGroup (Fin n) ℝ => zm hb c (κ : Matrix (Fin n) (Fin n) ℝ)) =
      fun κ : Matrix.unitaryGroup (Fin n) ℝ => (((κ : Matrix (Fin n) (Fin n) ℝ) (ia hb, c).1 (ia hb, c).2 : ℝ) : ℂ) +
        -Complex.I * (((κ : Matrix (Fin n) (Fin n) ℝ) (ib hb, c).1 (ib hb, c).2 : ℝ) : ℂ) := by
    funext κ
    rw [zm]
    ring
  rw [e]
  exact h

theorem isTranslateFinite_bf (hb : b + 1 < n) (c c' : Fin n) (m : ℕ) :
    IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => bf hb c c' m (κ : Matrix (Fin n) (Fin n) ℝ)) :=
  isTranslateFinite_add
    (isTranslateFinite_mul (isTranslateFinite_pow (isTranslateFinite_zp hb c) m)
      (isTranslateFinite_zp hb c'))
    (isTranslateFinite_mul (isTranslateFinite_pow (isTranslateFinite_zm hb c) m)
      (isTranslateFinite_zm hb c'))

theorem continuous_entry (i c : Fin n) :
    Continuous fun κ : Matrix (Fin n) (Fin n) ℝ => ((κ i c : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp ((continuous_apply c).comp (continuous_apply i))

theorem continuous_zp (hb : b + 1 < n) (c : Fin n) : Continuous (zp hb c) :=
  (continuous_entry _ _).add (continuous_const.mul (continuous_entry _ _))

theorem continuous_zm (hb : b + 1 < n) (c : Fin n) : Continuous (zm hb c) :=
  (continuous_entry _ _).sub (continuous_const.mul (continuous_entry _ _))

theorem continuous_bf (hb : b + 1 < n) (c c' : Fin n) (m : ℕ) : Continuous (bf hb c c' m) :=
  (((continuous_zp hb c).pow m).mul (continuous_zp hb c')).add
    (((continuous_zm hb c).pow m).mul (continuous_zm hb c'))

end TestVector

section Extension

open TranslateFinite PrincipalSeriesExtension GramFormula

theorem signReal_cases (x : ℝ) : signReal x = 1 ∨ signReal x = -1 := by
  unfold signReal
  split_ifs <;> simp

/-- **Test vectors.** A continuous `O(n)`-finite function `F` on matrices which transforms under
the sign matrices like the position characters of `ds` and whose block Fourier coefficients of
weight `|k| < |m|` vanish on `O(n)` at every induction block of weight `m` is the restriction to
`O(n)` of an `O(n)`-finite function of the standard module of `ds`. -/
theorem exists_KF {ds : List RealBlock} (hN : realRank ds = n)
    {F : Matrix (Fin n) (Fin n) ℝ → ℂ} (hFc : Continuous F)
    (hFt : IsTranslateFinite (id : Matrix.unitaryGroup (Fin n) ℝ → Matrix.unitaryGroup (Fin n) ℝ)
      (fun κ => F (κ : Matrix (Fin n) (Fin n) ℝ)))
    {q : Fin n → ℕ} (hq : IsSignEq q F)
    (hs : ∀ i : Fin n, (-1 : ℂ) ^ q i = realPositionCharacter ds i (-1))
    (hwin : ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
      ∀ k : ℤ, |k| < |d.weight| → ∀ κ : Matrix (Fin n) (Fin n) ℝ,
        κ ∈ Matrix.unitaryGroup (Fin n) ℝ →
        coeff k (fun φ => F ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ)) = 0) :
    ∃ v : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n), ∀ g ∈ unitaryCompact ℝ n,
      (v : Langlands.GeneralLinear n ℝ → ℂ) g = F (g : Matrix (Fin n) (Fin n) ℝ) := by
  have hsgn : ∀ (a : Fin n → ℝˣ) (κ : Matrix.unitaryGroup (Fin n) ℝ),
      F ((signDiagonal (fun i => (a i : ℝ)) * κ : Matrix.unitaryGroup (Fin n) ℝ) :
        Matrix (Fin n) (Fin n) ℝ) =
        principalSeriesCharacter ℝ n (realPositionCharacter ds) (fun i => signUnit (a i)) *
          F (κ : Matrix (Fin n) (Fin n) ℝ) := by
    intro a κ
    have hsd : ((signDiagonal (fun i => (a i : ℝ)) * κ : Matrix.unitaryGroup (Fin n) ℝ) :
        Matrix (Fin n) (Fin n) ℝ) =
        Matrix.diagonal (fun i => signReal (a i : ℝ)) * (κ : Matrix (Fin n) (Fin n) ℝ) := rfl
    rw [hsd, hq _ (fun i => signReal_cases _) _, JacquetKernel.principalSeriesCharacter_sign]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold signReal signUnit
    split_ifs
    · simp [RealStrictCharacterLanglandsQuotient.realPositionCharacter_one]
    · rw [← hs i]
      push_cast
      rfl
  obtain ⟨f, hf, hfK⟩ := principalSeriesExtension n ds
    (fun κ : Matrix.unitaryGroup (Fin n) ℝ => F (κ : Matrix (Fin n) (Fin n) ℝ))
    (hFc.comp continuous_subtype_val) hFt hsgn
  have hfK' : ∀ g ∈ unitaryCompact ℝ n, f g = F (g : Matrix (Fin n) (Fin n) ℝ) := by
    intro g hg
    have h := hfK ⟨(g : Matrix (Fin n) (Fin n) ℝ), hg⟩
    have hg' : (Unitary.toUnits (⟨(g : Matrix (Fin n) (Fin n) ℝ), hg⟩ :
        Matrix.unitaryGroup (Fin n) ℝ)) = g := Units.ext rfl
    rw [hg'] at h
    exact h
  refine ⟨⟨f, InductionStages.mem_realStandardModule_of_unitaryCompact hN hf.1 ?_, hf.2⟩, hfK'⟩
  intro p d hd k hk κ hκ
  rw [blockFourierCoefficient_eq_coeff]
  have h : (fun θ => f (blockRotation n p θ * κ)) = fun θ =>
      F ((blockRotation n p θ : Matrix (Fin n) (Fin n) ℝ) * (κ : Matrix (Fin n) (Fin n) ℝ)) := by
    funext θ
    rw [hfK' _ ((unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n p θ) hκ)]
    rfl
  rw [h]
  exact hwin p d hd k hk _ hκ

/-- Two modes `±N` of `F` along the rotations of `p` kill the coefficients of weight `|k| < |N|`. -/
theorem coeff_eq_zero_of_two_mode {F A B : Matrix (Fin n) (Fin n) ℝ → ℂ} {p : ℕ} {N : ℤ}
    (hAB : ∀ (φ : ℝ) (κ : Matrix (Fin n) (Fin n) ℝ),
      F ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ) =
        expMode N φ * A κ + expMode (-N) φ * B κ)
    {k : ℤ} (hk : |k| < |N|) (κ : Matrix (Fin n) (Fin n) ℝ) :
    coeff k (fun φ => F ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ)) = 0 := by
  have h : (fun φ => F ((blockRotation n p φ : Matrix (Fin n) (Fin n) ℝ) * κ)) =
      fun φ => expMode N φ * A κ + expMode (-N) φ * B κ := funext fun φ => hAB φ κ
  rw [h]
  exact coeff_two_mode_eq_zero _ _ hk

end Extension

end RealBlockTestVector

end Langlands.Archimedean
