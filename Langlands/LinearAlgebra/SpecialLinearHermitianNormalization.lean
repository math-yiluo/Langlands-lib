import Langlands.LinearAlgebra.SpecialLinearConjugationEquiv
import Langlands.GroupScheme.Examples.HermitianMatrixBasic

/-! # Hermitian normalization of a projectively involutive outer matrix -/

noncomputable section

universe u v w

namespace Langlands.LinearAlgebra.SpecialLinearHermitianNormalization

open Matrix
open Langlands.GroupScheme Langlands.GroupScheme.SU3Root
open Langlands.LinearAlgebra.SpecialLinearConjugation

variable {L : Type u} [Field L] {I : Type v} [Fintype I] [DecidableEq I]

/-- Elementary multiplicative Hilbert 90 for a nontrivial field involution. -/
theorem exists_hermitian_scaling_unit (c : RingInvolution L)
    (hnontrivial : ∃ x : L, c.bar x ≠ x) (a : L) (ha : c.bar a * a = 1) :
    ∃ b : Lˣ, c.bar (b : L) * a = (b : L) := by
  by_cases h : 1 + a = 0
  · obtain ⟨x, hx⟩ := hnontrivial
    have ha' : a = -1 := eq_neg_of_add_eq_zero_right h
    refine ⟨Units.mk0 (c.bar x - x) (sub_ne_zero.mpr hx), ?_⟩
    simp only [Units.val_mk0, map_sub, c.bar_bar, ha']
    ring
  · refine ⟨Units.mk0 (1 + a) h, ?_⟩
    simp only [Units.val_mk0, map_add, map_one, add_mul, one_mul, ha]
    exact add_comm _ _

omit [Fintype I] [DecidableEq I] in
/-- Adjoint is semilinear with respect to multiplication by a coefficient scalar. -/
theorem adjoint_smul (c : RingInvolution L) (a : L) (M : Matrix I I L) :
    HermitianMatrix.adjoint c (a • M) =
      c.bar a • HermitianMatrix.adjoint c M := by
  ext i j
  exact map_mul c.bar a (M j i)

variable [Nonempty I]

/-- The proportionality scalar of a nonsingular matrix and its adjoint has norm one. -/
theorem scalar_norm_one (c : RingInvolution L) (J : GeneralLinearGroup I L)
    (a : L) (hJ : HermitianMatrix.adjoint c (J : Matrix I I L) = a • (J : Matrix I I L)) :
    c.bar a * a = 1 := by
  have h := congrArg (HermitianMatrix.adjoint c) hJ
  rw [HermitianMatrix.adjoint_adjoint, adjoint_smul, hJ, smul_smul] at h
  apply smul_left_injective L (Units.ne_zero J)
  simpa only [one_smul] using h.symm

/-- A chosen unit scaling a supplied adjoint-proportional nonsingular matrix to be Hermitian. -/
def hermitianScalingUnit (c : RingInvolution L)
    (hnontrivial : ∃ x : L, c.bar x ≠ x) (J : GeneralLinearGroup I L)
    (a : L) (hJ : HermitianMatrix.adjoint c (J : Matrix I I L) = a • (J : Matrix I I L)) :
    Lˣ :=
  Classical.choose
    (exists_hermitian_scaling_unit c hnontrivial a (scalar_norm_one c J a hJ))

theorem hermitianScalingUnit_spec (c : RingInvolution L)
    (hnontrivial : ∃ x : L, c.bar x ≠ x) (J : GeneralLinearGroup I L)
    (a : L) (hJ : HermitianMatrix.adjoint c (J : Matrix I I L) = a • (J : Matrix I I L)) :
    c.bar (hermitianScalingUnit c hnontrivial J a hJ : L) * a =
      (hermitianScalingUnit c hnontrivial J a hJ : L) :=
  Classical.choose_spec
    (exists_hermitian_scaling_unit c hnontrivial a (scalar_norm_one c J a hJ))

omit [Nonempty I] in
private theorem coe_scalar_mul (b : Lˣ) (J : GeneralLinearGroup I L) :
    (GeneralLinearGroup.scalar I b * J : GeneralLinearGroup I L).val =
      (b : L) • (J : Matrix I I L) := by
  ext i j
  simp [GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_mul]

/-- The actual nonsingular Hermitian Gram matrix obtained by a chosen scalar multiple. -/
def hermitianForm (c : RingInvolution L)
    (hnontrivial : ∃ x : L, c.bar x ≠ x) (J : GeneralLinearGroup I L)
    (a : L) (hJ : HermitianMatrix.adjoint c (J : Matrix I I L) = a • (J : Matrix I I L)) :
    HermitianMatrix.Form c I where
  gram := GeneralLinearGroup.scalar I (hermitianScalingUnit c hnontrivial J a hJ) * J
  hermitian := by
    rw [coe_scalar_mul, adjoint_smul, hJ, smul_smul, hermitianScalingUnit_spec]

omit [Nonempty I] in
/-- Scalar multiplication has no effect on conjugation, after any coefficient map. -/
theorem map_scalar_mul_conjugate {R : Type w} [CommRing R] (f : L →+* R)
    (b : Lˣ) (J : GeneralLinearGroup I L) (g : GeneralLinearGroup I R) :
    GeneralLinearGroup.map f (GeneralLinearGroup.scalar I b * J) * g *
        (GeneralLinearGroup.map f (GeneralLinearGroup.scalar I b * J))⁻¹ =
      GeneralLinearGroup.map f J * g * (GeneralLinearGroup.map f J)⁻¹ := by
  let s := GeneralLinearGroup.scalar I (Units.map f.toMonoidHom b)
  have hcenter : s ∈ Subgroup.center _ := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  have hs := (Subgroup.mem_center_iff.mp hcenter
    (GeneralLinearGroup.map f J * g * (GeneralLinearGroup.map f J)⁻¹)).symm
  rw [map_mul, GeneralLinearGroup.map_scalar]
  change (s * GeneralLinearGroup.map f J) * g *
      (s * GeneralLinearGroup.map f J)⁻¹ = _
  calc
    _ = s * (GeneralLinearGroup.map f J * g * (GeneralLinearGroup.map f J)⁻¹) * s⁻¹ := by group
    _ = _ := by rw [hs]; group

/-- The inverse Gram matrix gives the same conjugation as the inverse supplied matrix. -/
theorem hermitianForm_inverse_conjugate {R : Type w} [CommRing R] (f : L →+* R)
    (c : RingInvolution L) (hnontrivial : ∃ x : L, c.bar x ≠ x)
    (J : GeneralLinearGroup I L) (a : L)
    (hJ : HermitianMatrix.adjoint c (J : Matrix I I L) = a • (J : Matrix I I L))
    (g : GeneralLinearGroup I R) :
    GeneralLinearGroup.map f (hermitianForm c hnontrivial J a hJ).gram⁻¹ * g *
        (GeneralLinearGroup.map f (hermitianForm c hnontrivial J a hJ).gram⁻¹)⁻¹ =
      GeneralLinearGroup.map f J⁻¹ * g * (GeneralLinearGroup.map f J⁻¹)⁻¹ := by
  have hc : (hermitianForm c hnontrivial J a hJ).gram⁻¹ =
      GeneralLinearGroup.scalar I (hermitianScalingUnit c hnontrivial J a hJ)⁻¹ * J⁻¹ := by
    change (GeneralLinearGroup.scalar I _ * J)⁻¹ = _
    rw [_root_.mul_inv_rev, ← map_inv]
    exact (Subgroup.mem_center_iff.mp
      (show GeneralLinearGroup.scalar I (hermitianScalingUnit c hnontrivial J a hJ)⁻¹ ∈
          Subgroup.center _ from by
        rw [GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨_, rfl⟩) J⁻¹)
  rw [hc]
  exact map_scalar_mul_conjugate f _ J⁻¹ g

omit [Nonempty I] in
/-- A projectively involutive outer representative gives an adjoint-proportional inverse matrix. -/
theorem inverse_adjoint_of_outer_square (c : RingInvolution L)
    (X : GeneralLinearGroup I L) (a : Lˣ)
    (hX : X * inverseTransposeGL (GeneralLinearGroup.map c.bar.toRingHom X) =
      GeneralLinearGroup.scalar I a) :
    HermitianMatrix.adjoint c (X⁻¹ : GeneralLinearGroup I L) =
      (a : L) • ((X⁻¹ : GeneralLinearGroup I L) : Matrix I I L) := by
  have h : inverseTransposeGL (GeneralLinearGroup.map c.bar.toRingHom X) =
      X⁻¹ * GeneralLinearGroup.scalar I a := by
    rw [← hX]
    group
  have hc : X⁻¹ * GeneralLinearGroup.scalar I a = GeneralLinearGroup.scalar I a * X⁻¹ :=
    Subgroup.mem_center_iff.mp (by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨a, rfl⟩) _
  have hm := congrArg (fun Q : GeneralLinearGroup I L => Q.val) (h.trans hc)
  rw [coe_scalar_mul] at hm
  exact hm

end Langlands.LinearAlgebra.SpecialLinearHermitianNormalization
