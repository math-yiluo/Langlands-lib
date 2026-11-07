import Langlands.GroupScheme.Examples.SU3MatrixGeneration

/-! # Special unitary matrices as actual fixed points in SL3 -/

noncomputable section

namespace Langlands.GroupScheme.SU3Root

universe u v

section Ring

variable {A : Type u} [CommRing A] (c : RingInvolution A)

/-- The same Gram matrix as an actual determinant-one matrix. -/
def weylSpecialLinear : Matrix.SpecialLinearGroup (Fin 3) A :=
  ⟨gram A, by simp [gram, Matrix.det_fin_three]⟩

@[simp] theorem weylSpecialLinear_val :
    (weylSpecialLinear (A := A) : Matrix (Fin 3) (Fin 3) A) = gram A := rfl

@[simp] theorem weylSpecialLinear_mul_self :
    (weylSpecialLinear : Matrix.SpecialLinearGroup (Fin 3) A) * weylSpecialLinear = 1 := by
  apply Subtype.ext
  exact congrArg Units.val (weylElement_mul_self (A := A))

@[simp] theorem weylSpecialLinear_mul_twice (g : Matrix.SpecialLinearGroup (Fin 3) A) :
    weylSpecialLinear * (weylSpecialLinear * g) = g := by
  rw [← mul_assoc, weylSpecialLinear_mul_self, one_mul]

/-- Conjugate transpose restricts to actual determinant-one matrices. -/
def conjugateTransposeSL (g : Matrix.SpecialLinearGroup (Fin 3) A) :
    Matrix.SpecialLinearGroup (Fin 3) A :=
  ⟨conjugateTranspose c (g : Matrix (Fin 3) (Fin 3) A), by
    change ((g : Matrix (Fin 3) (Fin 3) A).map c.bar).transpose.det = 1
    rw [Matrix.det_transpose]
    change (c.bar.toRingHom.mapMatrix (g : Matrix (Fin 3) (Fin 3) A)).det = 1
    rw [← RingHom.map_det c.bar.toRingHom]
    simp⟩

@[simp] theorem conjugateTransposeSL_val (g : Matrix.SpecialLinearGroup (Fin 3) A) :
    (conjugateTransposeSL c g : Matrix (Fin 3) (Fin 3) A) =
      conjugateTranspose c (g : Matrix (Fin 3) (Fin 3) A) := rfl

@[simp] theorem conjugateTransposeSL_one :
    conjugateTransposeSL c (1 : Matrix.SpecialLinearGroup (Fin 3) A) = 1 :=
  Subtype.ext (conjugateTranspose_one c)

theorem conjugateTransposeSL_mul (g h : Matrix.SpecialLinearGroup (Fin 3) A) :
    conjugateTransposeSL c (g * h) = conjugateTransposeSL c h * conjugateTransposeSL c g :=
  Subtype.ext (conjugateTranspose_mul c _ _)

@[simp] theorem conjugateTransposeSL_inv (g : Matrix.SpecialLinearGroup (Fin 3) A) :
    conjugateTransposeSL c g⁻¹ = (conjugateTransposeSL c g)⁻¹ := by
  apply mul_right_cancel (b := conjugateTransposeSL c g)
  rw [← conjugateTransposeSL_mul, mul_inv_cancel, conjugateTransposeSL_one, inv_mul_cancel]

@[simp] theorem conjugateTransposeSL_involutive (g : Matrix.SpecialLinearGroup (Fin 3) A) :
    conjugateTransposeSL c (conjugateTransposeSL c g) = g := by
  ext i j
  simp [conjugateTranspose]

@[simp] theorem conjugateTransposeSL_weyl :
    conjugateTransposeSL c (weylSpecialLinear : Matrix.SpecialLinearGroup (Fin 3) A) =
      weylSpecialLinear := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjugateTranspose, gram]

/-- The actual inverse-adjoint endomorphism whose fixed points are special unitary matrices. -/
def unitaryTwist : Matrix.SpecialLinearGroup (Fin 3) A →*
    Matrix.SpecialLinearGroup (Fin 3) A where
  toFun g := weylSpecialLinear * conjugateTransposeSL c g⁻¹ * weylSpecialLinear
  map_one' := by simp
  map_mul' g h := by
    simp only [mul_inv_rev, conjugateTransposeSL_mul]
    simp only [mul_assoc, weylSpecialLinear_mul_twice]

/-- The inverse-adjoint construction satisfies the defining cancellation identity. -/
theorem unitaryTwist_cancel (g : Matrix.SpecialLinearGroup (Fin 3) A) :
    conjugateTransposeSL c g * weylSpecialLinear * unitaryTwist c g =
      weylSpecialLinear := by
  change conjugateTransposeSL c g * weylSpecialLinear *
    (weylSpecialLinear * conjugateTransposeSL c g⁻¹ * weylSpecialLinear) = _
  simp only [mul_assoc, weylSpecialLinear_mul_twice]
  rw [← mul_assoc, ← conjugateTransposeSL_mul, inv_mul_cancel,
    conjugateTransposeSL_one, one_mul]

/-- Fixedness is exactly preservation of the specified Hermitian form. -/
theorem unitaryTwist_fixed_iff (g : Matrix.SpecialLinearGroup (Fin 3) A) :
    unitaryTwist c g = g ↔ PreservesForm c (g : Matrix (Fin 3) (Fin 3) A) := by
  have h := unitaryTwist_cancel c g
  constructor
  · intro hg
    rw [hg] at h
    exact congrArg Subtype.val h
  · intro hg
    apply mul_left_cancel (a := conjugateTransposeSL c g * weylSpecialLinear)
    rw [h]
    apply Subtype.ext
    exact hg.symm

/-- The actual subgroup fixed by inverse adjoint inside the special linear group. -/
def twistFixedSubgroup : Subgroup (Matrix.SpecialLinearGroup (Fin 3) A) :=
  (unitaryTwist c).eqLocus (MonoidHom.id _)

@[simp] theorem mem_twistFixedSubgroup (g : Matrix.SpecialLinearGroup (Fin 3) A) :
    g ∈ twistFixedSubgroup c ↔
      PreservesForm c (g : Matrix (Fin 3) (Fin 3) A) :=
  unitaryTwist_fixed_iff c g

/-- The actual SL3 fixed subgroup and GL3 determinant-one isometry subgroup coincide
under the usual inclusion of special linear matrices into general linear matrices. -/
def fixedSpecialUnitaryEquiv : twistFixedSubgroup c ≃* specialUnitarySubgroup c where
  toFun g := ⟨Matrix.SpecialLinearGroup.toGL g.1,
    (mem_twistFixedSubgroup c g.1).mp g.2,
    Matrix.SpecialLinearGroup.coeToGL_det g.1⟩
  invFun g := ⟨⟨(g.1 : Matrix (Fin 3) (Fin 3) A), congrArg Units.val g.2.2⟩,
    (mem_twistFixedSubgroup c _).mpr g.2.1⟩
  left_inv g := by
    apply Subtype.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    rfl
  map_mul' g h := by
    apply Subtype.ext
    exact Matrix.SpecialLinearGroup.toGL.map_mul g.1 h.1

@[simp] theorem fixedSpecialUnitaryEquiv_val (g : twistFixedSubgroup c) :
    (fixedSpecialUnitaryEquiv c g).1 = Matrix.SpecialLinearGroup.toGL g.1 := rfl

end Ring

section Naturality

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  {c : RingInvolution A} {d : RingInvolution B}

@[simp] theorem map_weylSpecialLinear (f : A →+* B) :
    Matrix.SpecialLinearGroup.map f (weylSpecialLinear : Matrix.SpecialLinearGroup (Fin 3) A) =
      weylSpecialLinear := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram]

theorem conjugateTransposeSL_map (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (g : Matrix.SpecialLinearGroup (Fin 3) A) :
    conjugateTransposeSL d (Matrix.SpecialLinearGroup.map f g) =
      Matrix.SpecialLinearGroup.map f (conjugateTransposeSL c g) := by
  ext i j
  simp [conjugateTranspose, hf]

/-- Every involution-compatible coefficient map commutes with the actual twist. -/
theorem unitaryTwist_map (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (g : Matrix.SpecialLinearGroup (Fin 3) A) :
    unitaryTwist d (Matrix.SpecialLinearGroup.map f g) =
      Matrix.SpecialLinearGroup.map f (unitaryTwist c g) := by
  change weylSpecialLinear * conjugateTransposeSL d (Matrix.SpecialLinearGroup.map f g)⁻¹ *
    weylSpecialLinear = Matrix.SpecialLinearGroup.map f
      (weylSpecialLinear * conjugateTransposeSL c g⁻¹ * weylSpecialLinear)
  rw [← map_inv, conjugateTransposeSL_map f hf, map_mul, map_mul, map_weylSpecialLinear]

end Naturality

end Langlands.GroupScheme.SU3Root
