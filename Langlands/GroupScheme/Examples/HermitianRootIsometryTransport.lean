import Langlands.GroupScheme.Examples.HermitianRootMatrixNaturality

/-! # Isometry transport of actual Hermitian matrix groups -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v w

variable {A : Type u} {B : Type w} {ι : Type v}
  [CommRing A] [CommRing B] [Fintype ι] [DecidableEq ι]
  {c : RingInvolution A} {d : RingInvolution B}
  {H J : DiagonalForm c ι} {H' J' : DiagonalForm d ι}

/-- Inverting a Gram congruence reverses the source and target forms. -/
theorem gramCongruence_inv (P : Matrix.GeneralLinearGroup (Index ι) A)
    (hP : conjugateTranspose c (P : Matrix (Index ι) (Index ι) A) * gram J *
      (P : Matrix (Index ι) (Index ι) A) = gram H) :
    conjugateTranspose c (P⁻¹ : Matrix.GeneralLinearGroup (Index ι) A) * gram H *
      ((P⁻¹ : Matrix.GeneralLinearGroup (Index ι) A) :
        Matrix (Index ι) (Index ι) A) = gram J := by
  calc
    _ = conjugateTranspose c (P⁻¹ : Matrix.GeneralLinearGroup (Index ι) A) *
        (conjugateTranspose c (P : Matrix (Index ι) (Index ι) A) * gram J *
          (P : Matrix (Index ι) (Index ι) A)) *
        ((P⁻¹ : Matrix.GeneralLinearGroup (Index ι) A) :
          Matrix (Index ι) (Index ι) A) := by rw [hP]
    _ = conjugateTranspose c
        ((P * P⁻¹ : Matrix.GeneralLinearGroup (Index ι) A) :
          Matrix (Index ι) (Index ι) A) * gram J *
        ((P * P⁻¹ : Matrix.GeneralLinearGroup (Index ι) A) :
          Matrix (Index ι) (Index ι) A) := by
      rw [Units.val_mul, conjugateTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = gram J := by simp

/-- Conjugation by an isometry carries actual form preservers to form preservers. -/
theorem preservesForm_isometry_conj (P : Matrix.GeneralLinearGroup (Index ι) A)
    (hP : conjugateTranspose c (P : Matrix (Index ι) (Index ι) A) * gram J *
      (P : Matrix (Index ι) (Index ι) A) = gram H)
    (g : Matrix.GeneralLinearGroup (Index ι) A)
    (hg : PreservesForm H (g : Matrix (Index ι) (Index ι) A)) :
    PreservesForm J (P * g * P⁻¹ : Matrix.GeneralLinearGroup (Index ι) A) := by
  unfold PreservesForm at *
  simp only [Units.val_mul, conjugateTranspose_mul]
  calc
    _ = conjugateTranspose c (P⁻¹ : Matrix.GeneralLinearGroup (Index ι) A) *
        (conjugateTranspose c (g : Matrix (Index ι) (Index ι) A) *
          (conjugateTranspose c (P : Matrix (Index ι) (Index ι) A) * gram J *
            (P : Matrix (Index ι) (Index ι) A)) *
          (g : Matrix (Index ι) (Index ι) A)) *
        ((P⁻¹ : Matrix.GeneralLinearGroup (Index ι) A) :
          Matrix (Index ι) (Index ι) A) := by
      simp only [Matrix.mul_assoc]
    _ = gram J := by rw [hP, hg]; exact gramCongruence_inv P hP

/-- An invertible Gram congruence identifies the determinant-one isometry groups.
Its determinant need not be one, and no middle weight needs to be a unit. -/
def specialUnitaryIsometryEquiv (P : Matrix.GeneralLinearGroup (Index ι) A)
    (hP : conjugateTranspose c (P : Matrix (Index ι) (Index ι) A) * gram J *
      (P : Matrix (Index ι) (Index ι) A) = gram H) :
    specialUnitarySubgroup H ≃* specialUnitarySubgroup J where
  toFun g := ⟨P * g.1 * P⁻¹, preservesForm_isometry_conj P hP g.1 g.2.1, by
    change Matrix.GeneralLinearGroup.det (P * g.1 * P⁻¹) = 1
    have hd : Matrix.GeneralLinearGroup.det g.1 = 1 := g.2.2
    simp only [map_mul, map_inv, hd, mul_one, mul_inv_cancel]⟩
  invFun g := ⟨P⁻¹ * g.1 * (P⁻¹)⁻¹,
    preservesForm_isometry_conj P⁻¹ (gramCongruence_inv P hP) g.1 g.2.1, by
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
    (P : Matrix.GeneralLinearGroup (Index ι) A)
    (hP : conjugateTranspose c (P : Matrix (Index ι) (Index ι) A) * gram J *
      (P : Matrix (Index ι) (Index ι) A) = gram H)
    (g : specialUnitarySubgroup H) :
    (specialUnitaryIsometryEquiv P hP g).1 = P * g.1 * P⁻¹ := rfl

/-- The inverse equivalence uses the inverse actual change-of-basis matrix. -/
@[simp] theorem specialUnitaryIsometryEquiv_symm_val
    (P : Matrix.GeneralLinearGroup (Index ι) A)
    (hP : conjugateTranspose c (P : Matrix (Index ι) (Index ι) A) * gram J *
      (P : Matrix (Index ι) (Index ι) A) = gram H)
    (g : specialUnitarySubgroup J) :
    ((specialUnitaryIsometryEquiv P hP).symm g).1 = P⁻¹ * g.1 * P := by
  change P⁻¹ * g.1 * (P⁻¹)⁻¹ = _
  rw [inv_inv]

/-- Compatible coefficient change carries a Gram congruence to the new forms. -/
theorem gramCongruence_map (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = H'.weight i)
    (hJ : ∀ i, f (J.weight i) = J'.weight i)
    (P : Matrix.GeneralLinearGroup (Index ι) A)
    (hP : conjugateTranspose c (P : Matrix (Index ι) (Index ι) A) * gram J *
      (P : Matrix (Index ι) (Index ι) A) = gram H) :
    conjugateTranspose d
        (Matrix.GeneralLinearGroup.map f P : Matrix (Index ι) (Index ι) B) *
      gram J' * (Matrix.GeneralLinearGroup.map f P : Matrix (Index ι) (Index ι) B) =
      gram H' := by
  change conjugateTranspose d ((P : Matrix (Index ι) (Index ι) A).map f) *
    gram J' * (P : Matrix (Index ι) (Index ι) A).map f = gram H'
  rw [gram_map f hH, gram_map f hJ, conjugateTranspose_map f hf,
    ← Matrix.map_mul, ← Matrix.map_mul, hP]

/-- Isometry transport commutes with every compatible coefficient homomorphism. -/
theorem specialUnitaryIsometryEquiv_map (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hH : ∀ i, f (H.weight i) = H'.weight i)
    (hJ : ∀ i, f (J.weight i) = J'.weight i)
    (P : Matrix.GeneralLinearGroup (Index ι) A)
    (hP : conjugateTranspose c (P : Matrix (Index ι) (Index ι) A) * gram J *
      (P : Matrix (Index ι) (Index ι) A) = gram H)
    (g : specialUnitarySubgroup H) :
    specialUnitaryMap f hf hJ (specialUnitaryIsometryEquiv P hP g) =
      specialUnitaryIsometryEquiv (Matrix.GeneralLinearGroup.map f P)
        (gramCongruence_map f hf hH hJ P hP) (specialUnitaryMap f hf hH g) := by
  apply Subtype.ext
  change Matrix.GeneralLinearGroup.map f (P * g.1 * P⁻¹) =
    Matrix.GeneralLinearGroup.map f P * Matrix.GeneralLinearGroup.map f g.1 *
      (Matrix.GeneralLinearGroup.map f P)⁻¹
  rw [map_mul, map_mul, map_inv]

end Langlands.GroupScheme.HermitianRoot
