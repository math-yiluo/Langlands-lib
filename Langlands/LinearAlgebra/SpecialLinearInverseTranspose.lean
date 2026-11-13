import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-! # Inverse transpose is not inner in matrix size at least three -/

noncomputable section

universe u v

namespace Langlands.LinearAlgebra.SpecialLinearInverseTranspose

open Matrix

variable {I : Type u} {R : Type v} [Fintype I] [DecidableEq I] [CommRing R]

/-- The inverse-transpose group homomorphism of the special linear group. -/
def inverseTranspose : SpecialLinearGroup I R →* SpecialLinearGroup I R where
  toFun g := (g⁻¹).transpose
  map_one' := by
    apply Subtype.ext
    simp [SpecialLinearGroup.transpose]
  map_mul' g h := by
    apply Subtype.ext
    simp only [_root_.mul_inv_rev, SpecialLinearGroup.coe_transpose, SpecialLinearGroup.coe_mul,
      Matrix.transpose_mul]

/-- Inverse transpose exchanges the indices of a transvection and negates its entry. -/
theorem inverseTranspose_transvection {i j : I} (hij : i ≠ j) (a : R) :
    (inverseTranspose (SpecialLinearGroup.transvection hij a) : Matrix I I R) =
      Matrix.transvection j i (-a) := by
  change (((SpecialLinearGroup.transvection hij a)⁻¹ : SpecialLinearGroup I R) :
    Matrix I I R).transpose = _
  rw [SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_coe]
  simp [Matrix.transvection, Matrix.transpose_single]

/-- A putative inner representative of inverse transpose kills a row away from a
supplied transvection index. -/
theorem row_entry_eq_zero {X : GeneralLinearGroup I R}
    (hX : ∀ g : SpecialLinearGroup I R,
      X * SpecialLinearGroup.toGL (inverseTranspose g) * X⁻¹ = SpecialLinearGroup.toGL g)
    {i j : I} (hij : i ≠ j) (b : I) (hb : b ≠ i) : X j b = 0 := by
  have he := (mul_inv_eq_iff_eq_mul).mp (hX (SpecialLinearGroup.transvection hij (1 : R)))
  have hm := congrArg (fun z : GeneralLinearGroup I R => (z : Matrix I I R)) he
  change (X : Matrix I I R) *
      (inverseTranspose (SpecialLinearGroup.transvection hij (1 : R)) : Matrix I I R) =
    (SpecialLinearGroup.transvection hij (1 : R) : Matrix I I R) * (X : Matrix I I R) at hm
  rw [inverseTranspose_transvection, SpecialLinearGroup.transvection_coe] at hm
  have h := congrArg (fun z : Matrix I I R => z i b) hm
  change ((X : Matrix I I R) * Matrix.transvection j i (-1) : Matrix I I R) i b =
    (Matrix.transvection i j 1 * (X : Matrix I I R) : Matrix I I R) i b at h
  rw [Matrix.mul_transvection_apply_of_ne j i i b hb,
    Matrix.transvection_mul_apply_same, one_mul] at h
  exact add_eq_left.mp h.symm

variable [Nontrivial R]

/-- With three distinct indices, no invertible matrix represents inverse transpose
as an inner automorphism of the special linear group. -/
theorem not_inner (i j k : I) (hij : i ≠ j) (hkj : k ≠ j) (hik : i ≠ k)
    (X : GeneralLinearGroup I R) :
    ¬ ∀ g : SpecialLinearGroup I R,
      X * SpecialLinearGroup.toGL (inverseTranspose g) * X⁻¹ = SpecialLinearGroup.toGL g := by
  intro hX
  have hrow (b : I) : X j b = 0 := by
    by_cases hb : b = i
    · subst b
      exact row_entry_eq_zero hX hkj i hik
    · exact row_entry_eq_zero hX hij b hb
  have h := congrArg (fun z : GeneralLinearGroup I R => z j j) (mul_inv_cancel X)
  change ((X * X⁻¹ : GeneralLinearGroup I R) : Matrix I I R) j j = (1 : Matrix I I R) j j at h
  simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Matrix.one_apply_eq,
    hrow, zero_mul, Finset.sum_const_zero] at h
  exact zero_ne_one h

/-- The opposite orientation of the same non-inner assertion. -/
theorem conjugation_ne_inverseTranspose (i j k : I) (hij : i ≠ j) (hkj : k ≠ j)
    (hik : i ≠ k) (X : GeneralLinearGroup I R) :
    ¬ ∀ g : SpecialLinearGroup I R,
      X * SpecialLinearGroup.toGL g * X⁻¹ = SpecialLinearGroup.toGL (inverseTranspose g) := by
  intro hX
  apply not_inner i j k hij hkj hik X⁻¹
  intro g
  rw [← hX g]
  group

/-- In the type-A matrix size `n+1`, inverse transpose is not inner for `n ≥ 2`. -/
theorem not_inner_fin {n : ℕ} (hn : 2 ≤ n) (X : GeneralLinearGroup (Fin (n + 1)) R) :
    ¬ ∀ g : SpecialLinearGroup (Fin (n + 1)) R,
      X * SpecialLinearGroup.toGL (inverseTranspose g) * X⁻¹ = SpecialLinearGroup.toGL g :=
  not_inner (⟨0, by omega⟩ : Fin (n + 1)) ⟨1, by omega⟩ ⟨2, by omega⟩
    (by intro h; have hh : (0 : ℕ) = 1 := congrArg Fin.val h; omega)
    (by intro h; have hh : (2 : ℕ) = 1 := congrArg Fin.val h; omega)
    (by intro h; have hh : (0 : ℕ) = 2 := congrArg Fin.val h; omega) X

end Langlands.LinearAlgebra.SpecialLinearInverseTranspose
