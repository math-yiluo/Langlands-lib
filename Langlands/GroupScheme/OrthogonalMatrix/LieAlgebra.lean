import Langlands.GroupScheme.OrthogonalMatrix.Subgroups
import Langlands.GroupScheme.SymplecticMatrix.LieAlgebra

/-! # Matrix coordinates on the Lie algebra of the split orthogonal group

A dual-number matrix `1 + εY` is orthogonal exactly when `Y Q + Q Yᵀ` is alternating. In
coordinates this says `Y J + J Yᵀ = 0` and `Y (inl a) (inr a) = Y (inr a) (inl a) = 0` for all
`a`. Through the inclusion into `GL_{l ⊕ l}` this identifies the Lie algebra of the split
orthogonal group with these matrices.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.OrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l]

/-! ### The Lie condition in coordinates -/

section Condition

variable {A : Type*} [CommRing A]

theorem mul_formMatrix_apply_inl (Y : Matrix (l ⊕ l) (l ⊕ l) A) (x : l ⊕ l) (b : l) :
    (Y * formMatrix l A) x (Sum.inl b) = 0 := by
  simp [formMatrix, Matrix.mul_apply, Fintype.sum_sum_type]

theorem mul_formMatrix_apply_inr (Y : Matrix (l ⊕ l) (l ⊕ l) A) (x : l ⊕ l) (b : l) :
    (Y * formMatrix l A) x (Sum.inr b) = Y x (Sum.inl b) := by
  simp [formMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem formMatrix_mul_transpose_apply_inl (Y : Matrix (l ⊕ l) (l ⊕ l) A) (a : l)
    (y : l ⊕ l) : (formMatrix l A * Yᵀ) (Sum.inl a) y = Y y (Sum.inr a) := by
  simp [formMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem formMatrix_mul_transpose_apply_inr (Y : Matrix (l ⊕ l) (l ⊕ l) A) (a : l)
    (y : l ⊕ l) : (formMatrix l A * Yᵀ) (Sum.inr a) y = 0 := by
  simp [formMatrix, Matrix.mul_apply, Fintype.sum_sum_type]

/-- **The orthogonal Lie condition in coordinates.** `Y Q + Q Yᵀ` is alternating exactly when
`Y J + J Yᵀ = 0` and the entries `Y (inl a) (inr a)` and `Y (inr a) (inl a)` vanish. -/
theorem isAlt_lie_iff (Y : Matrix (l ⊕ l) (l ⊕ l) A) :
    IsAlt (Y * formMatrix l A + formMatrix l A * Yᵀ) ↔
      Y * polarMatrix l A + polarMatrix l A * Yᵀ = 0 ∧
        ∀ a, Y (Sum.inl a) (Sum.inr a) = 0 ∧ Y (Sum.inr a) (Sum.inl a) = 0 := by
  rw [isAlt_iff]
  have hsum : Y * formMatrix l A + formMatrix l A * Yᵀ +
      (Y * formMatrix l A + formMatrix l A * Yᵀ)ᵀ =
      Y * polarMatrix l A + polarMatrix l A * Yᵀ := by
    rw [← formMatrix_add_transpose, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul]
    abel
  rw [hsum]
  refine and_congr Iff.rfl ⟨fun h a => ⟨?_, ?_⟩, fun h i => ?_⟩
  · have := h (Sum.inl a)
    rwa [Matrix.add_apply, mul_formMatrix_apply_inl, formMatrix_mul_transpose_apply_inl,
      zero_add] at this
  · have := h (Sum.inr a)
    rwa [Matrix.add_apply, mul_formMatrix_apply_inr, formMatrix_mul_transpose_apply_inr,
      add_zero] at this
  · rcases i with a | a
    · rw [Matrix.add_apply, mul_formMatrix_apply_inl, formMatrix_mul_transpose_apply_inl,
        zero_add]
      exact (h a).1
    · rw [Matrix.add_apply, mul_formMatrix_apply_inr, formMatrix_mul_transpose_apply_inr,
        add_zero]
      exact (h a).2

end Condition

/-! ### Dual-number orthogonal matrices -/

section DualNumber

open GeneralLinear.DualNumber

variable {A : Type u} [CommRing A]

omit [Fintype l] in
theorem formMatrix_dualNumber :
    formMatrix l (DualNumber A) = (formMatrix l A).map (TrivSqZeroExt.inlHom A A) :=
  (formMatrix_map _).symm

/-- `(1 + εY) Q (1 + εY)ᵀ - Q = ε (Y Q + Q Yᵀ)`. -/
theorem defect_one_add_epsilonMatrix (Y : Matrix (l ⊕ l) (l ⊕ l) A) :
    defect (1 + epsilonMatrix Y) =
      epsilonMatrix (Y * formMatrix l A + formMatrix l A * Y.transpose) := by
  have hT : (epsilonMatrix Y).transpose = epsilonMatrix Y.transpose := rfl
  rw [defect, formMatrix_dualNumber, Matrix.transpose_add, Matrix.transpose_one, hT]
  simp only [add_mul, mul_add, one_mul, mul_one, epsilonMatrix_mul_constantMatrix,
    constantMatrix_mul_epsilonMatrix, epsilonMatrix_mul, add_zero, epsilonMatrix_add]
  abel

omit [Fintype l] [DecidableEq l] in
/-- An `ε`-matrix is alternating exactly when its coefficient matrix is. -/
theorem isAlt_epsilonMatrix_iff (M : Matrix (l ⊕ l) (l ⊕ l) A) :
    IsAlt (epsilonMatrix M) ↔ IsAlt M := by
  constructor
  · rintro ⟨V, hV⟩
    refine ⟨V.map TrivSqZeroExt.snd, ?_⟩
    ext i j
    have h := congrArg (fun N : Matrix (l ⊕ l) (l ⊕ l) (DualNumber A) =>
      TrivSqZeroExt.snd (N i j)) hV
    simpa using h
  · rintro ⟨U, rfl⟩
    refine ⟨epsilonMatrix U, ?_⟩
    apply Matrix.ext
    intro i j
    simp only [epsilonMatrix_apply, Matrix.sub_apply, Matrix.transpose_apply,
      TrivSqZeroExt.inr_sub]

/-- `1 + εY` is orthogonal exactly when `Y Q + Q Yᵀ` is alternating. -/
theorem one_add_epsilonMatrix_mem_iff (Y : Matrix (l ⊕ l) (l ⊕ l) A) :
    1 + epsilonMatrix Y ∈ orthogonalGroup l (DualNumber A) ↔
      IsAlt (Y * formMatrix l A + formMatrix l A * Y.transpose) := by
  rw [mem_orthogonalGroup_iff, defect_one_add_epsilonMatrix, isAlt_epsilonMatrix_iff]

end DualNumber

/-! ### Affine points -/

section AffinePoints

variable (l) (R : CommRingCat.{u})

/-- Points on affine test schemes are orthogonal matrices over the test algebra. -/
def affinePointsEquiv (S : CommAlgCat.{u} R) :
    ((algSpec R).obj (op S) ⟶ (groupScheme l R).X) ≃* orthogonalGroup l S :=
  Corepresented.affinePointsEquiv (functor l R) (corepresentableBy l R) S

variable {l R}

/-- On affine points, the inclusion into `GL_{l ⊕ l}` is the inclusion of matrices. -/
theorem affinePointsEquiv_inclusion (S : CommAlgCat.{u} R)
    (f : (algSpec R).obj (op S) ⟶ (groupScheme l R).X) :
    GeneralLinear.affinePointsEquiv (l ⊕ l) R S (f ≫ (inclusion l R).hom.hom) =
      toGL (affinePointsEquiv l R S f) :=
  Corepresented.groupSchemeMap_affinePoints _ _ _ f

/-- On affine points, the Levi embedding is the Levi block matrix. -/
theorem affinePointsEquiv_leviMap (S : CommAlgCat.{u} R)
    (f : (algSpec R).obj (op S) ⟶ (GeneralLinear.groupScheme l R).X) :
    affinePointsEquiv l R S (f ≫ (leviMap R).hom.hom) =
      leviHom S (GeneralLinear.affinePointsEquiv l R S f) :=
  Corepresented.groupSchemeMap_affinePoints _ _ _ f

end AffinePoints

/-! ### Lie coordinates -/

section Lie

open GeneralLinear.DualNumber

variable {R : CommRingCat.{u}} {A : Type u} [CommRing A] [Algebra R A]

/-- The matrix coordinates of the Lie algebra of `O_{2l}`, through the inclusion into
`GL_{l ⊕ l}` and the published coordinates of the Lie algebra of `GL`. -/
def lieMatrix : Additive (lieKernel (groupScheme l R) A) →ₗ[A]
    Matrix (l ⊕ l) (l ⊕ l) A :=
  (pointKernelLinearEquiv (n := l ⊕ l) (R := R) (A := A)).symm.toLinearMap ∘ₗ
    Lie.targetMapLinear (inclusion l R) A

theorem pointKernelLinearEquiv_lieMatrix (X : Additive (lieKernel (groupScheme l R) A)) :
    pointKernelLinearEquiv (lieMatrix X) = Lie.targetMapLinear (inclusion l R) A X :=
  LinearEquiv.apply_symm_apply _ _

/-- The inclusion of `O_{2l}` into `GL` is a monomorphism of schemes. -/
instance mono_inclusion : Mono (inclusion l R).hom.hom := by
  constructor
  intro Z g h hgh
  apply (pointsEquiv l R Z).injective
  have h1 := congrArg (GeneralLinear.pointsEquiv (l ⊕ l) R Z) hgh
  rw [pointsEquiv_inclusion, pointsEquiv_inclusion] at h1
  apply Subtype.ext
  exact congrArg (fun g : GL (l ⊕ l) Γ(Z.left, ⊤) => g.val) h1

theorem lieMatrix_injective :
    Function.Injective (lieMatrix (l := l) (R := R) (A := A)) :=
  (pointKernelLinearEquiv (n := l ⊕ l) (R := R) (A := A)).symm.injective.comp
    (Lie.targetMapLinear_injective (inclusion l R) A)

/-- The affine dual-number matrix of an element of the Lie kernel of `O_{2l}` is `1 + εY` for
its coordinate matrix `Y`. -/
theorem affinePointsEquiv_lieKernel (X : Additive (lieKernel (groupScheme l R) A)) :
    ((affinePointsEquiv l R (CommAlgCat.of R (DualNumber A)) X.toMul.val :
        orthogonalGroup l (DualNumber A)) : Matrix (l ⊕ l) (l ⊕ l) (DualNumber A)) =
      1 + epsilonMatrix (lieMatrix X) := by
  have h1 := pointKernelLinearEquiv_lieMatrix X
  have h2 := congrArg (fun x : Additive (lieKernel (GeneralLinear.groupScheme (l ⊕ l) R) A) =>
    GeneralLinear.affinePointsEquiv (l ⊕ l) R (CommAlgCat.of R (DualNumber A)) x.toMul.val) h1
  simp only [pointKernelLinearEquiv_toMul, pointKernelEquiv_val, lieKernelHomLinear_val] at h2
  have h4 := affinePointsEquiv_inclusion (l := l) (R := R) (CommAlgCat.of R (DualNumber A))
    X.toMul.val
  have h5 := pointUnit_matrix (R := R) (lieMatrix X)
  have h6 := h4.symm.trans (h2.symm.trans h5)
  exact congrArg (fun g : GL (l ⊕ l) (DualNumber A) => g.val) h6

/-- The Lie algebra of `O_{2l}` consists of matrices `Y` with `Y Q + Q Yᵀ` alternating. -/
theorem isAlt_lieMatrix (X : Additive (lieKernel (groupScheme l R) A)) :
    IsAlt (lieMatrix X * formMatrix l A + formMatrix l A * (lieMatrix X).transpose) := by
  rw [← one_add_epsilonMatrix_mem_iff, ← affinePointsEquiv_lieKernel]
  exact (affinePointsEquiv l R (CommAlgCat.of R (DualNumber A)) X.toMul.val).property

/-- Conversely every matrix `Y` with `Y Q + Q Yᵀ` alternating is the coordinate matrix of an
element of the Lie algebra of `O_{2l}`. -/
theorem exists_lieMatrix_eq (Y : Matrix (l ⊕ l) (l ⊕ l) A)
    (hY : IsAlt (Y * formMatrix l A + formMatrix l A * Y.transpose)) :
    ∃ X : Additive (lieKernel (groupScheme l R) A), lieMatrix X = Y := by
  let g : orthogonalGroup l (DualNumber A) :=
    ⟨1 + epsilonMatrix Y, (one_add_epsilonMatrix_mem_iff Y).mpr hY⟩
  let p := (affinePointsEquiv l R (CommAlgCat.of R (DualNumber A))).symm g
  have hp : p ≫ (inclusion l R).hom.hom = (pointUnit Y : GeneralLinear.DualNumber.AffinePoints
      (l ⊕ l) R (DualNumber A)) := by
    apply (GeneralLinear.affinePointsEquiv (l ⊕ l) R (CommAlgCat.of R (DualNumber A))).injective
    rw [affinePointsEquiv_inclusion, pointUnit_matrix]
    apply Units.ext
    change ((affinePointsEquiv l R _ p : orthogonalGroup l (DualNumber A)) :
      Matrix (l ⊕ l) (l ⊕ l) (DualNumber A)) = 1 + epsilonMatrix Y
    rw [MulEquiv.apply_symm_apply]
  have hred : Lie.reduction (groupScheme l R) p = 1 := by
    apply (cancel_mono (inclusion l R).hom.hom).mp
    rw [MonObj.one_comp]
    have h : Lie.reduction (groupScheme l R) p ≫ (inclusion l R).hom.hom =
        Lie.reduction (GeneralLinear.groupScheme (l ⊕ l) R) (p ≫ (inclusion l R).hom.hom) :=
      Category.assoc _ _ _
    rw [h, hp]
    exact pointReduction_pointUnit Y
  refine ⟨Additive.ofMul ⟨p, hred⟩, ?_⟩
  apply (pointKernelLinearEquiv (n := l ⊕ l) (R := R) (A := A)).injective
  rw [pointKernelLinearEquiv_lieMatrix]
  apply Additive.toMul.injective
  apply Subtype.ext
  exact hp

end Lie

end Langlands.GroupScheme.OrthogonalMatrix
