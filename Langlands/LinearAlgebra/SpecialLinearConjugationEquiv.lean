import Langlands.LinearAlgebra.SpecialLinearInverseTranspose

/-! # Natural conjugation equivalences and inverse transpose -/

noncomputable section

universe u v w

namespace Langlands.LinearAlgebra.SpecialLinearConjugation

open Matrix

variable {I : Type u} [Fintype I] [DecidableEq I]
  {R : Type v} [CommRing R] {S : Type w} [CommRing S]

/-- Conjugation by an invertible matrix preserves determinant one. -/
def conjugate (X : GeneralLinearGroup I R) (g : SpecialLinearGroup I R) :
    SpecialLinearGroup I R :=
  ⟨(X * SpecialLinearGroup.toGL g * X⁻¹ : GeneralLinearGroup I R), by
    change ((GeneralLinearGroup.det (X * SpecialLinearGroup.toGL g * X⁻¹)) : R) = 1
    simp⟩

@[simp] theorem toGL_conjugate (X : GeneralLinearGroup I R) (g : SpecialLinearGroup I R) :
    SpecialLinearGroup.toGL (conjugate X g) =
      X * SpecialLinearGroup.toGL g * X⁻¹ := Units.ext rfl

/-- Conjugation, as an automorphism of the special linear group. -/
def conjugationEquiv (X : GeneralLinearGroup I R) :
    SpecialLinearGroup I R ≃* SpecialLinearGroup I R where
  toFun := conjugate X
  invFun := conjugate X⁻¹
  left_inv g := by
    apply SpecialLinearGroup.toGL_injective
    simp only [toGL_conjugate, inv_inv]
    group
  right_inv g := by
    apply SpecialLinearGroup.toGL_injective
    simp only [toGL_conjugate, inv_inv]
    group
  map_mul' g h := by
    apply SpecialLinearGroup.toGL_injective
    simp only [toGL_conjugate, map_mul]
    group

@[simp] theorem conjugationEquiv_apply (X : GeneralLinearGroup I R)
    (g : SpecialLinearGroup I R) : conjugationEquiv X g = conjugate X g := rfl

@[simp] theorem conjugationEquiv_symm (X : GeneralLinearGroup I R) :
    (conjugationEquiv X).symm = conjugationEquiv X⁻¹ := by
  apply MulEquiv.ext
  intro g
  rfl

/-- The inclusion of `SL` into `GL` commutes with coefficient maps. -/
@[simp] theorem toGL_map (f : R →+* S) (g : SpecialLinearGroup I R) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map f g) =
      GeneralLinearGroup.map f (SpecialLinearGroup.toGL g) := Units.ext rfl

/-- Conjugation commutes with every coefficient homomorphism. -/
theorem map_conjugate (f : R →+* S) (X : GeneralLinearGroup I R)
    (g : SpecialLinearGroup I R) :
    SpecialLinearGroup.map f (conjugate X g) =
      conjugate (GeneralLinearGroup.map f X) (SpecialLinearGroup.map f g) := by
  apply SpecialLinearGroup.toGL_injective
  simp only [toGL_map, toGL_conjugate, map_mul, map_inv]

/-- Inverse transpose on the general linear group. -/
def inverseTransposeGL : GeneralLinearGroup I R →* GeneralLinearGroup I R where
  toFun X :=
    { val := (X⁻¹ : GeneralLinearGroup I R).val.transpose
      inv := X.val.transpose
      val_inv := by
        rw [← Matrix.transpose_mul]
        change (X.val * X.inv).transpose = 1
        rw [X.val_inv, Matrix.transpose_one]
      inv_val := by
        rw [← Matrix.transpose_mul]
        change (X.inv * X.val).transpose = 1
        rw [X.inv_val, Matrix.transpose_one] }
  map_one' := by
    apply Units.ext
    simp
  map_mul' X Y := by
    apply Units.ext
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

@[simp] theorem coe_inverseTransposeGL (X : GeneralLinearGroup I R) :
    (inverseTransposeGL X : Matrix I I R) =
      (X⁻¹ : GeneralLinearGroup I R).val.transpose := rfl

/-- Applying inverse transpose twice gives the original invertible matrix. -/
@[simp] theorem inverseTransposeGL_involutive (X : GeneralLinearGroup I R) :
    inverseTransposeGL (inverseTransposeGL X) = X := by
  apply Units.ext
  exact Matrix.transpose_transpose X.val

/-- Inverse transpose commutes with coefficient maps on `GL`. -/
theorem inverseTransposeGL_map (f : R →+* S) (X : GeneralLinearGroup I R) :
    inverseTransposeGL (GeneralLinearGroup.map f X) =
      GeneralLinearGroup.map f (inverseTransposeGL X) := by
  apply Units.ext
  rfl

/-- The `GL` and `SL` inverse-transpose operations agree under inclusion. -/
@[simp] theorem toGL_inverseTranspose (g : SpecialLinearGroup I R) :
    SpecialLinearGroup.toGL (SpecialLinearInverseTranspose.inverseTranspose g) =
      inverseTransposeGL (SpecialLinearGroup.toGL g) := Units.ext rfl

/-- Inverse transpose takes conjugation by `X` to conjugation by its inverse transpose. -/
theorem inverseTranspose_conjugate (X : GeneralLinearGroup I R)
    (g : SpecialLinearGroup I R) :
    SpecialLinearInverseTranspose.inverseTranspose (conjugate X g) =
      conjugate (inverseTransposeGL X) (SpecialLinearInverseTranspose.inverseTranspose g) := by
  apply SpecialLinearGroup.toGL_injective
  simp only [toGL_inverseTranspose, toGL_conjugate, map_mul, map_inv]

end Langlands.LinearAlgebra.SpecialLinearConjugation
