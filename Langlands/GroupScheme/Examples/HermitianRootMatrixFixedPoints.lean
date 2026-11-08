import Langlands.GroupScheme.Examples.HermitianRootOpposites

/-! # Fixed matrices for a nondegenerate diagonal Hermitian form -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v w

variable {A : Type u} {B : Type w} {ι : Type v}
  [CommRing A] [CommRing B] [Fintype ι] [DecidableEq ι]
  {c : RingInvolution A} {d : RingInvolution B}

/-- The genuine inverse Gram matrix, using unit middle weights. -/
def inverseGram (w : ι → Aˣ) : Matrix (Index ι) (Index ι) A :=
  Matrix.fromBlocks 0
    (Matrix.of fun _ j => Sum.elim (fun _ => 0) (fun _ => 1) j)
    (Matrix.of fun i _ => Sum.elim (fun _ => 0) (fun _ => 1) i)
    (Matrix.fromBlocks (-Matrix.diagonal (fun i => (((w i)⁻¹ : Aˣ) : A))) 0 0 0)

theorem gram_mul_inverseGram (H : DiagonalForm c ι) (w : ι → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i) : gram H * inverseGram w = 1 := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [gram, inverseGram, Matrix.fromBlocks, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.diagonal_apply, Matrix.one_apply, ← hw]
  split_ifs with h
  · subst j; simp
  · simp

theorem inverseGram_mul_gram (H : DiagonalForm c ι) (w : ι → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i) : inverseGram w * gram H = 1 := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [gram, inverseGram, Matrix.fromBlocks, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.diagonal_apply, Matrix.one_apply, ← hw]
  split_ifs with h
  · subst j; simp
  · simp

/-- The actual invertible Gram matrix, without a determinant-one requirement. -/
def gramElement (H : DiagonalForm c ι) (w : ι → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i) : Matrix.GeneralLinearGroup (Index ι) A :=
  ⟨gram H, inverseGram w, gram_mul_inverseGram H w hw, inverseGram_mul_gram H w hw⟩

@[simp] theorem gramElement_val (H : DiagonalForm c ι) (w : ι → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i) :
    (gramElement H w hw : Matrix (Index ι) (Index ι) A) = gram H := rfl

/-- Conjugate transpose restricts to determinant-one matrices in every middle dimension. -/
def conjugateTransposeSL (c : RingInvolution A) (g : Matrix.SpecialLinearGroup (Index ι) A) :
    Matrix.SpecialLinearGroup (Index ι) A :=
  ⟨conjugateTranspose c (g : Matrix (Index ι) (Index ι) A), by
    change ((g : Matrix (Index ι) (Index ι) A).map c.bar).transpose.det = 1
    rw [Matrix.det_transpose]
    change (c.bar.toRingHom.mapMatrix (g : Matrix (Index ι) (Index ι) A)).det = 1
    rw [← RingHom.map_det c.bar.toRingHom]
    simp⟩

@[simp] theorem conjugateTransposeSL_val (g : Matrix.SpecialLinearGroup (Index ι) A) :
    (conjugateTransposeSL c g : Matrix (Index ι) (Index ι) A) =
      conjugateTranspose c (g : Matrix (Index ι) (Index ι) A) := rfl

@[simp] theorem conjugateTransposeSL_one :
    conjugateTransposeSL c (1 : Matrix.SpecialLinearGroup (Index ι) A) = 1 :=
  Subtype.ext conjugateTranspose_one

theorem conjugateTransposeSL_mul (g h : Matrix.SpecialLinearGroup (Index ι) A) :
    conjugateTransposeSL c (g * h) = conjugateTransposeSL c h * conjugateTransposeSL c g :=
  Subtype.ext (conjugateTranspose_mul _ _)

@[simp] theorem conjugateTransposeSL_inv (g : Matrix.SpecialLinearGroup (Index ι) A) :
    conjugateTransposeSL c g⁻¹ = (conjugateTransposeSL c g)⁻¹ := by
  apply mul_right_cancel (b := conjugateTransposeSL c g)
  rw [← conjugateTransposeSL_mul, mul_inv_cancel, conjugateTransposeSL_one, inv_mul_cancel]

/-- Inverse conjugate transpose is an actual special-linear group endomorphism. -/
def inverseAdjoint (c : RingInvolution A) :
    Matrix.SpecialLinearGroup (Index ι) A →* Matrix.SpecialLinearGroup (Index ι) A where
  toFun g := conjugateTransposeSL c g⁻¹
  map_one' := by simp
  map_mul' g h := by simp only [mul_inv_rev, conjugateTransposeSL_mul]

/-- Conjugation by the inverse Gram matrix preserves the special-linear group. -/
def gramConjugation (H : DiagonalForm c ι) (w : ι → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i) :
    Matrix.SpecialLinearGroup (Index ι) A →* Matrix.SpecialLinearGroup (Index ι) A where
  toFun g := ⟨((gramElement H w hw)⁻¹ * Matrix.SpecialLinearGroup.toGL g *
    gramElement H w hw : Matrix.GeneralLinearGroup (Index ι) A), by
      have h : Matrix.GeneralLinearGroup.det
          ((gramElement H w hw)⁻¹ * Matrix.SpecialLinearGroup.toGL g *
            gramElement H w hw) = 1 := by
        simp only [map_mul, map_inv, Matrix.SpecialLinearGroup.coeToGL_det, mul_one,
          inv_mul_cancel]
      exact congrArg Units.val h⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by
    apply Subtype.ext
    change (((gramElement H w hw)⁻¹ * Matrix.SpecialLinearGroup.toGL (g * h) *
      gramElement H w hw : Matrix.GeneralLinearGroup (Index ι) A) :
        Matrix (Index ι) (Index ι) A) = _
    rw [map_mul]
    exact congrArg Units.val (show
      (gramElement H w hw)⁻¹ * (Matrix.SpecialLinearGroup.toGL g *
        Matrix.SpecialLinearGroup.toGL h) * gramElement H w hw =
      ((gramElement H w hw)⁻¹ * Matrix.SpecialLinearGroup.toGL g * gramElement H w hw) *
        ((gramElement H w hw)⁻¹ * Matrix.SpecialLinearGroup.toGL h * gramElement H w hw)
      by simp only [mul_assoc, mul_inv_cancel_left])

/-- Inverse adjoint for the full weighted Gram form. -/
def unitaryTwist (H : DiagonalForm c ι) (w : ι → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i) :
    Matrix.SpecialLinearGroup (Index ι) A →* Matrix.SpecialLinearGroup (Index ι) A :=
  (gramConjugation H w hw).comp (inverseAdjoint c)

theorem toGL_unitaryTwist (H : DiagonalForm c ι) (w : ι → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i) (g : Matrix.SpecialLinearGroup (Index ι) A) :
    Matrix.SpecialLinearGroup.toGL (unitaryTwist H w hw g) =
      (gramElement H w hw)⁻¹ * Matrix.SpecialLinearGroup.toGL (conjugateTransposeSL c g⁻¹) *
        gramElement H w hw := by
  apply Units.ext
  rfl

theorem unitaryTwist_cancel (H : DiagonalForm c ι) (w : ι → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i) (g : Matrix.SpecialLinearGroup (Index ι) A) :
    Matrix.SpecialLinearGroup.toGL (conjugateTransposeSL c g) * gramElement H w hw *
      Matrix.SpecialLinearGroup.toGL (unitaryTwist H w hw g) = gramElement H w hw := by
  rw [toGL_unitaryTwist, conjugateTransposeSL_inv, map_inv]
  simp only [mul_assoc, mul_inv_cancel_left]

/-- Fixedness is exactly preservation of the original full weighted Hermitian form. -/
theorem unitaryTwist_fixed_iff (H : DiagonalForm c ι) (w : ι → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i) (g : Matrix.SpecialLinearGroup (Index ι) A) :
    unitaryTwist H w hw g = g ↔ PreservesForm H (g : Matrix (Index ι) (Index ι) A) := by
  have h := unitaryTwist_cancel H w hw g
  constructor
  · intro hg
    rw [hg] at h
    exact congrArg Units.val h
  · intro hg
    apply Matrix.SpecialLinearGroup.toGL_injective
    apply mul_left_cancel (a := Matrix.SpecialLinearGroup.toGL (conjugateTransposeSL c g) *
      gramElement H w hw)
    rw [h]
    apply Units.ext
    exact hg.symm

/-- The subgroup of actual special-linear matrices fixed by the weighted inverse adjoint. -/
def twistFixedSubgroup (H : DiagonalForm c ι) (w : ι → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i) : Subgroup (Matrix.SpecialLinearGroup (Index ι) A) :=
  (unitaryTwist H w hw).eqLocus (MonoidHom.id _)

/-- Fixed special-linear matrices are precisely the actual determinant-one isometries. -/
def fixedSpecialUnitaryEquiv (H : DiagonalForm c ι) (w : ι → Aˣ)
    (hw : ∀ i, (w i : A) = H.weight i) :
    twistFixedSubgroup H w hw ≃* specialUnitarySubgroup H where
  toFun g := ⟨Matrix.SpecialLinearGroup.toGL g.1,
    (unitaryTwist_fixed_iff H w hw g.1).mp g.2,
    Matrix.SpecialLinearGroup.coeToGL_det g.1⟩
  invFun g := ⟨⟨(g.1 : Matrix (Index ι) (Index ι) A), congrArg Units.val g.2.2⟩,
    (unitaryTwist_fixed_iff H w hw _).mpr g.2.1⟩
  left_inv g := by apply Subtype.ext; rfl
  right_inv g := by apply Subtype.ext; apply Units.ext; rfl
  map_mul' g h := by
    apply Subtype.ext
    exact Matrix.SpecialLinearGroup.toGL.map_mul g.1 h.1

end Langlands.GroupScheme.HermitianRoot
