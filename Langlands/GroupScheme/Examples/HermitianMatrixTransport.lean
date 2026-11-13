import Langlands.GroupScheme.Examples.HermitianMatrixBasic

/-! # Isometry transport of actual Hermitian matrix groups -/

namespace Langlands.GroupScheme.HermitianMatrix

open SU3Root

universe u v w

variable {A : Type u} {B : Type w} {ι : Type v}
  [CommRing A] [CommRing B] [Fintype ι] [DecidableEq ι]
  {c : RingInvolution A} {d : RingInvolution B}
  {H J : Form c ι} {H' J' : Form d ι}

/-- Inverting a Gram congruence reverses the source and target forms. -/
theorem gramCongruence_inv (P : Matrix.GeneralLinearGroup (ι) A)
    (hP : adjoint c (P : Matrix (ι) (ι) A) * (J.gram : Matrix ι ι A) *
      (P : Matrix (ι) (ι) A) = (H.gram : Matrix ι ι A)) :
    adjoint c (P⁻¹ : Matrix.GeneralLinearGroup (ι) A) * (H.gram : Matrix ι ι A) *
      ((P⁻¹ : Matrix.GeneralLinearGroup (ι) A) :
        Matrix (ι) (ι) A) = (J.gram : Matrix ι ι A) := by
  calc
    _ = adjoint c (P⁻¹ : Matrix.GeneralLinearGroup (ι) A) *
        (adjoint c (P : Matrix (ι) (ι) A) * (J.gram : Matrix ι ι A) *
          (P : Matrix (ι) (ι) A)) *
        ((P⁻¹ : Matrix.GeneralLinearGroup (ι) A) :
          Matrix (ι) (ι) A) := by rw [hP]
    _ = adjoint c
        ((P * P⁻¹ : Matrix.GeneralLinearGroup (ι) A) :
          Matrix (ι) (ι) A) * (J.gram : Matrix ι ι A) *
        ((P * P⁻¹ : Matrix.GeneralLinearGroup (ι) A) :
          Matrix (ι) (ι) A) := by
      rw [Units.val_mul, adjoint_mul]
      simp only [Matrix.mul_assoc]
    _ = (J.gram : Matrix ι ι A) := by simp

/-- Conjugation by an isometry carries actual form preservers to form preservers. -/
theorem preserves_isometry_conj (P : Matrix.GeneralLinearGroup (ι) A)
    (hP : adjoint c (P : Matrix (ι) (ι) A) * (J.gram : Matrix ι ι A) *
      (P : Matrix (ι) (ι) A) = (H.gram : Matrix ι ι A))
    (g : Matrix.GeneralLinearGroup (ι) A)
    (hg : Preserves H (g : Matrix (ι) (ι) A)) :
    Preserves J (P * g * P⁻¹ : Matrix.GeneralLinearGroup (ι) A) := by
  unfold Preserves at *
  simp only [Units.val_mul, adjoint_mul]
  calc
    _ = adjoint c (P⁻¹ : Matrix.GeneralLinearGroup (ι) A) *
        (adjoint c (g : Matrix (ι) (ι) A) *
          (adjoint c (P : Matrix (ι) (ι) A) * (J.gram : Matrix ι ι A) *
            (P : Matrix (ι) (ι) A)) *
          (g : Matrix (ι) (ι) A)) *
        ((P⁻¹ : Matrix.GeneralLinearGroup (ι) A) :
          Matrix (ι) (ι) A) := by
      simp only [Matrix.mul_assoc]
    _ = (J.gram : Matrix ι ι A) := by rw [hP, hg]; exact gramCongruence_inv P hP

/-- An invertible Gram congruence identifies the determinant-one isometry groups.
The change-of-basis determinant is arbitrary. -/
def specialUnitaryIsometryEquiv (P : Matrix.GeneralLinearGroup (ι) A)
    (hP : adjoint c (P : Matrix (ι) (ι) A) * (J.gram : Matrix ι ι A) *
      (P : Matrix (ι) (ι) A) = (H.gram : Matrix ι ι A)) :
    specialUnitarySubgroup H ≃* specialUnitarySubgroup J where
  toFun g := ⟨P * g.1 * P⁻¹, preserves_isometry_conj P hP g.1 g.2.1, by
    change Matrix.GeneralLinearGroup.det (P * g.1 * P⁻¹) = 1
    have hd : Matrix.GeneralLinearGroup.det g.1 = 1 := g.2.2
    simp only [map_mul, map_inv, hd, mul_one, mul_inv_cancel]⟩
  invFun g := ⟨P⁻¹ * g.1 * (P⁻¹)⁻¹,
    preserves_isometry_conj P⁻¹ (gramCongruence_inv P hP) g.1 g.2.1, by
      change Matrix.GeneralLinearGroup.det (P⁻¹ * g.1 * (P⁻¹)⁻¹) = 1
      have hd : Matrix.GeneralLinearGroup.det g.1 = 1 := g.2.2
      simp only [map_mul, map_inv, hd, mul_one, mul_inv_cancel]⟩
  left_inv g := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv g := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' g h := Subtype.ext ((MulAut.conj P).map_mul g.1 h.1)

@[simp] theorem specialUnitaryIsometryEquiv_val
    (P : Matrix.GeneralLinearGroup (ι) A)
    (hP : adjoint c (P : Matrix (ι) (ι) A) * (J.gram : Matrix ι ι A) *
      (P : Matrix (ι) (ι) A) = (H.gram : Matrix ι ι A))
    (g : specialUnitarySubgroup H) :
    (specialUnitaryIsometryEquiv P hP g).1 = P * g.1 * P⁻¹ := rfl

/-- The inverse equivalence uses the inverse actual change-of-basis matrix. -/
@[simp] theorem specialUnitaryIsometryEquiv_symm_val
    (P : Matrix.GeneralLinearGroup (ι) A)
    (hP : adjoint c (P : Matrix (ι) (ι) A) * (J.gram : Matrix ι ι A) *
      (P : Matrix (ι) (ι) A) = (H.gram : Matrix ι ι A))
    (g : specialUnitarySubgroup J) :
    ((specialUnitaryIsometryEquiv P hP).symm g).1 = P⁻¹ * g.1 * P := by
  change P⁻¹ * g.1 * (P⁻¹)⁻¹ = _
  rw [inv_inv]

/-- Compatible coefficient change carries a Gram congruence to the new forms. -/
theorem gramCongruence_map (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : (H.gram : Matrix ι ι A).map f = H'.gram)
    (hJ : (J.gram : Matrix ι ι A).map f = J'.gram)
    (P : Matrix.GeneralLinearGroup (ι) A)
    (hP : adjoint c (P : Matrix (ι) (ι) A) * (J.gram : Matrix ι ι A) *
      (P : Matrix (ι) (ι) A) = (H.gram : Matrix ι ι A)) :
    adjoint d
        (Matrix.GeneralLinearGroup.map f P : Matrix (ι) (ι) B) *
      (J'.gram : Matrix ι ι B) * (Matrix.GeneralLinearGroup.map f P : Matrix (ι) (ι) B) =
      (H'.gram : Matrix ι ι B) := by
  change adjoint d ((P : Matrix (ι) (ι) A).map f) *
    (J'.gram : Matrix ι ι B) * (P : Matrix (ι) (ι) A).map f = (H'.gram : Matrix ι ι B)
  rw [← hH, ← hJ, adjoint_map f hf,
    ← Matrix.map_mul, ← Matrix.map_mul, hP]

/-- Isometry transport commutes with every compatible coefficient homomorphism. -/
theorem specialUnitaryIsometryEquiv_map (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : (H.gram : Matrix ι ι A).map f = H'.gram)
    (hJ : (J.gram : Matrix ι ι A).map f = J'.gram)
    (P : Matrix.GeneralLinearGroup (ι) A)
    (hP : adjoint c (P : Matrix (ι) (ι) A) * (J.gram : Matrix ι ι A) *
      (P : Matrix (ι) (ι) A) = (H.gram : Matrix ι ι A))
    (g : specialUnitarySubgroup H) :
    coefficientMap f hf hJ (specialUnitaryIsometryEquiv P hP g) =
      specialUnitaryIsometryEquiv (Matrix.GeneralLinearGroup.map f P)
        (gramCongruence_map f hf hH hJ P hP) (coefficientMap f hf hH g) := by
  apply Subtype.ext
  change Matrix.GeneralLinearGroup.map f (P * g.1 * P⁻¹) =
    Matrix.GeneralLinearGroup.map f P * Matrix.GeneralLinearGroup.map f g.1 *
      (Matrix.GeneralLinearGroup.map f P)⁻¹
  rw [map_mul, map_mul, map_inv]

end Langlands.GroupScheme.HermitianMatrix
