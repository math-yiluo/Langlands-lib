import Langlands.Representation.Archimedean.RealStandardModuleFourier
import Langlands.Representation.Archimedean.RealJacquetReduction
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The block rotations `r_p(θ)` in closed form

`blockRotation N p θ = exp(θ W)` with `W = E_{p+1,p} - E_{p,p+1}`. When `p + 1 < N` it equals
`1 + (cos θ - 1) P + sin θ W` with `P = E_{p,p} + E_{p+1,p+1}`. This module also proves the group
law, `2π`-periodicity, the entries, `r_p(π) = s_p s_{p+1}`, conjugation by the sign matrices
`s_j`, and the commutation of rotations in disjoint blocks.
-/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealBlockRotation

variable {N : ℕ}

/-- The first coordinate `p` of the block, as an index. -/
def ia {N p : ℕ} (h : p + 1 < N) : Fin N := ⟨p, by omega⟩

/-- The second coordinate `p + 1` of the block, as an index. -/
def ib {N p : ℕ} (h : p + 1 < N) : Fin N := ⟨p + 1, h⟩

theorem ia_ne_ib {N p : ℕ} (h : p + 1 < N) : ia h ≠ ib h := by
  intro e
  have := congrArg Fin.val e
  simp [ia, ib] at this

/-- The projection `E_{p,p} + E_{p+1,p+1}` onto the coordinates of the block. -/
def blockProj {N p : ℕ} (h : p + 1 < N) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.single (ia h) (ia h) 1 + Matrix.single (ib h) (ib h) 1

theorem rotationGenerator_eq {N p : ℕ} (h : p + 1 < N) :
    rotationGenerator N p = Matrix.single (ib h) (ia h) 1 - Matrix.single (ia h) (ib h) 1 := by
  ext i j
  simp only [rotationGenerator, Matrix.of_apply, Matrix.sub_apply, Matrix.single_apply, ia, ib,
    Fin.ext_iff]
  split_ifs <;> (try norm_num) <;> omega

theorem gen_mul_gen {N p : ℕ} (h : p + 1 < N) :
    rotationGenerator N p * rotationGenerator N p = -blockProj h := by
  have hne := ia_ne_ib h
  rw [rotationGenerator_eq h, blockProj]
  simp only [sub_mul, mul_sub, Matrix.single_mul_single_same, mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_mul_single_of_ne _ _ _ _ hne.symm]
  abel

theorem gen_mul_proj {N p : ℕ} (h : p + 1 < N) :
    rotationGenerator N p * blockProj h = rotationGenerator N p := by
  have hne := ia_ne_ib h
  rw [rotationGenerator_eq h, blockProj]
  simp only [sub_mul, mul_add, Matrix.single_mul_single_same, mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_mul_single_of_ne _ _ _ _ hne.symm]
  abel

theorem proj_mul_gen {N p : ℕ} (h : p + 1 < N) :
    blockProj h * rotationGenerator N p = rotationGenerator N p := by
  have hne := ia_ne_ib h
  rw [rotationGenerator_eq h, blockProj]
  simp only [mul_sub, add_mul, Matrix.single_mul_single_same, one_mul,
    Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_mul_single_of_ne _ _ _ _ hne.symm]
  abel

/-- The closed form `1 + (cos θ - 1) P + sin θ W`. -/
def rotMatrix {N p : ℕ} (h : p + 1 < N) (θ : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  1 + (Real.cos θ - 1) • blockProj h + Real.sin θ • rotationGenerator N p

theorem hasDerivAt_rotMatrix {N p : ℕ} (h : p + 1 < N) (θ : ℝ) :
    HasDerivAt (rotMatrix h) (rotationGenerator N p * rotMatrix h θ) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (Real.cos t - 1) • blockProj h)
      ((-Real.sin θ) • blockProj h) θ :=
    ((Real.hasDerivAt_cos θ).sub_const 1).smul_const _
  have h2 : HasDerivAt (fun t : ℝ => Real.sin t • rotationGenerator N p)
      (Real.cos θ • rotationGenerator N p) θ :=
    (Real.hasDerivAt_sin θ).smul_const _
  have h3 := (h1.const_add (1 : Matrix (Fin N) (Fin N) ℝ)).add h2
  refine h3.congr_deriv ?_
  rw [rotMatrix, mul_add, mul_add, mul_one, Matrix.mul_smul, Matrix.mul_smul, gen_mul_proj h,
    gen_mul_gen h]
  module

theorem blockRotation_val_eq {N p : ℕ} (h : p + 1 < N) (θ : ℝ) :
    (blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) = rotMatrix h θ := by
  set W := rotationGenerator N p with hW
  -- `t ↦ exp(-t W) M(t)` has derivative zero
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (-W)) * rotMatrix h t) 0 t := by
    intro t
    have he := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-W) t
    have := he.mul (hasDerivAt_rotMatrix h t)
    refine this.congr_deriv ?_
    rw [mul_neg, neg_mul, mul_assoc, neg_add_cancel]
  have hc : ∀ t : ℝ, NormedSpace.exp (t • (-W)) * rotMatrix h t = 1 := by
    intro t
    have := is_const_of_deriv_eq_zero (f := fun t : ℝ => NormedSpace.exp (t • (-W)) * rotMatrix h t)
      (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
    rw [this]
    simp [rotMatrix]
  have hcomm : Commute (θ • W) (θ • (-W)) := ((Commute.refl W).neg_right).smul_left θ |>.smul_right θ
  calc (blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ)
      = NormedSpace.exp (θ • W) * (NormedSpace.exp (θ • (-W)) * rotMatrix h θ) := by
        rw [hc, mul_one, blockRotation_val]
    _ = rotMatrix h θ := by
        rw [← mul_assoc, ← Matrix.exp_add_of_commute _ _ hcomm, smul_neg, add_neg_cancel,
          NormedSpace.exp_zero, one_mul]

/-! ## Group law and periodicity -/

theorem blockRotation_add (N p : ℕ) (θ φ : ℝ) :
    blockRotation N p (θ + φ) = blockRotation N p θ * blockRotation N p φ := by
  ext1
  simp only [blockRotation_val, Units.val_mul, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left θ).smul_right φ)

theorem blockRotation_zero (N p : ℕ) : blockRotation N p 0 = 1 := by
  ext1
  simp

theorem blockRotation_neg (N p : ℕ) (θ : ℝ) :
    blockRotation N p (-θ) = (blockRotation N p θ)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← blockRotation_add, neg_add_cancel, blockRotation_zero]

theorem blockRotation_two_pi {N p : ℕ} (h : p + 1 < N) :
    blockRotation N p (2 * Real.pi) = 1 := by
  ext1
  rw [blockRotation_val_eq h]
  simp [rotMatrix]

theorem blockRotation_add_two_pi {N p : ℕ} (h : p + 1 < N) (θ : ℝ) :
    blockRotation N p (θ + 2 * Real.pi) = blockRotation N p θ := by
  rw [blockRotation_add, blockRotation_two_pi h, mul_one]

/-! ## Entries -/

theorem blockProj_apply {N p : ℕ} (h : p + 1 < N) (i j : Fin N) :
    blockProj h i j = if i = j ∧ ((i : ℕ) = p ∨ (i : ℕ) = p + 1) then 1 else 0 := by
  simp only [blockProj, Matrix.add_apply, Matrix.single_apply, ia, ib, Fin.ext_iff]
  split_ifs <;> (try norm_num) <;> omega

theorem rotationGenerator_apply (N p : ℕ) (i j : Fin N) :
    rotationGenerator N p i j =
      if (i : ℕ) = p + 1 ∧ (j : ℕ) = p then 1
      else if (i : ℕ) = p ∧ (j : ℕ) = p + 1 then -1 else 0 := rfl

/-- The entries of `r_p(θ)`: `cos θ` at `(p, p)` and `(p+1, p+1)`, `sin θ` at `(p+1, p)`,
`-sin θ` at `(p, p+1)`, and those of the identity elsewhere. -/
theorem blockRotation_apply {N p : ℕ} (h : p + 1 < N) (θ : ℝ) (i j : Fin N) :
    (blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) i j =
      if (i : ℕ) = p + 1 ∧ (j : ℕ) = p then Real.sin θ
      else if (i : ℕ) = p ∧ (j : ℕ) = p + 1 then -Real.sin θ
      else if i = j ∧ ((i : ℕ) = p ∨ (i : ℕ) = p + 1) then Real.cos θ
      else if i = j then 1 else 0 := by
  rw [blockRotation_val_eq h, rotMatrix]
  simp only [Matrix.add_apply, Matrix.smul_apply, blockProj_apply, rotationGenerator_apply,
    Matrix.one_apply, smul_eq_mul, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | ring1

/-! ## The rotation by `π` and the sign matrices -/

/-- `r_p(π) = s_p s_{p+1}`. -/
theorem blockRotation_pi {N p : ℕ} (h : p + 1 < N) :
    blockRotation N p Real.pi =
      Unitary.toUnits (signReflection N (ia h)) * Unitary.toUnits (signReflection N (ib h)) := by
  ext i j
  rw [blockRotation_apply h, Units.val_mul, Unitary.val_toUnits_apply, Unitary.val_toUnits_apply,
    signReflection_val, signReflection_val, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  simp only [Real.sin_pi, Real.cos_pi, ia, ib, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | ring1

/-- Conjugating `r_p(θ)` by the sign matrix `s_j` gives `r_p(-θ)` if `j ∈ {p, p+1}`. -/
theorem signReflection_mul_blockRotation_mul_of_mem {N p : ℕ} (h : p + 1 < N) (j : Fin N)
    (hj : (j : ℕ) = p ∨ (j : ℕ) = p + 1) (θ : ℝ) :
    Unitary.toUnits (signReflection N j) * blockRotation N p θ *
        Unitary.toUnits (signReflection N j) = blockRotation N p (-θ) := by
  ext i k
  rw [Units.val_mul, Units.val_mul, Unitary.val_toUnits_apply, signReflection_val,
    Matrix.mul_diagonal, Matrix.diagonal_mul, blockRotation_apply h, blockRotation_apply h,
    Real.sin_neg, Real.cos_neg]
  simp only [Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | ring1

/-- The sign matrix `s_j` commutes with `r_p(θ)` if `j ∉ {p, p+1}`. -/
theorem signReflection_mul_blockRotation_mul_of_not_mem {N p : ℕ} (h : p + 1 < N) (j : Fin N)
    (hj : (j : ℕ) ≠ p ∧ (j : ℕ) ≠ p + 1) (θ : ℝ) :
    Unitary.toUnits (signReflection N j) * blockRotation N p θ *
        Unitary.toUnits (signReflection N j) = blockRotation N p θ := by
  ext i k
  rw [Units.val_mul, Units.val_mul, Unitary.val_toUnits_apply, signReflection_val,
    Matrix.mul_diagonal, Matrix.diagonal_mul, blockRotation_apply h]
  simp only [Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | ring1

/-! ## Disjoint blocks commute -/

theorem rotationGenerator_mul_eq_zero {N p p' : ℕ} (hd : p + 1 < p' ∨ p' + 1 < p) :
    rotationGenerator N p * rotationGenerator N p' = 0 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  simp only [rotationGenerator_apply]
  split_ifs <;> first | (exfalso; omega) | ring1

/-- Rotations in disjoint blocks commute. -/
theorem blockRotation_commute {N p p' : ℕ} (hd : p + 1 < p' ∨ p' + 1 < p) (θ φ : ℝ) :
    blockRotation N p θ * blockRotation N p' φ = blockRotation N p' φ * blockRotation N p θ := by
  have hW : Commute (rotationGenerator N p) (rotationGenerator N p') :=
    (rotationGenerator_mul_eq_zero hd).trans (rotationGenerator_mul_eq_zero hd.symm).symm
  have hc : Commute (θ • rotationGenerator N p) (φ • rotationGenerator N p') :=
    (hW.smul_left θ).smul_right φ
  ext1
  simp only [Units.val_mul, blockRotation_val]
  rw [← Matrix.exp_add_of_commute _ _ hc, ← Matrix.exp_add_of_commute _ _ hc.symm, add_comm]

end RealBlockRotation

end Langlands.Archimedean
