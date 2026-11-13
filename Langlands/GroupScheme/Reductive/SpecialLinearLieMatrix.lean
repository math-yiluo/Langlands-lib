import Langlands.GroupScheme.SpecialLinearTorus
import Langlands.GroupScheme.SpecialLinear
import Langlands.GroupScheme.Lie.GeneralLinearAdjoint
import Langlands.GroupScheme.Lie.Functoriality
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Matrix coordinates on the Lie algebra of the special linear group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear.FinSucc

variable {n : Type} [Fintype n] [DecidableEq n]

/-! ### Dual-number determinants -/

section DualNumber

open GeneralLinear.DualNumber

variable {A : Type u} [CommRing A]

/-- `det (1 + εY) = 1 + ε tr Y` over the dual numbers. -/
theorem det_one_add_epsilonMatrix (Y : Matrix n n A) :
    (1 + epsilonMatrix Y).det = 1 + TrivSqZeroExt.inr Y.trace := by
  have he : (DualNumber.eps : DualNumber A) • Y.map (TrivSqZeroExt.inlHom A A) =
      epsilonMatrix Y := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, TrivSqZeroExt.inlHom_apply,
      epsilonMatrix_apply, DualNumber.inr_eq_smul_eps, ← TrivSqZeroExt.inl_mul_eq_smul,
      (DualNumber.commute_eps_left _).eq]
  have h := Matrix.det_one_add_smul (DualNumber.eps : DualNumber A)
    (Y.map (TrivSqZeroExt.inlHom A A))
  rw [he] at h
  rw [h, pow_two, DualNumber.eps_mul_eps, mul_zero, add_zero]
  congr 1
  rw [← AddMonoidHom.map_trace, TrivSqZeroExt.inlHom_apply, DualNumber.inr_eq_smul_eps,
    ← TrivSqZeroExt.inl_mul_eq_smul]

omit [Fintype n] [DecidableEq n] in
theorem epsilonMatrix_eq_zero_iff (Y : Matrix n n A) :
    epsilonMatrix Y = 0 ↔ Y = 0 := by
  constructor
  · intro h
    ext i j
    have h1 := congrArg (fun M : Matrix n n (DualNumber A) => TrivSqZeroExt.snd (M i j)) h
    simpa using h1
  · rintro rfl
    exact epsilonMatrix_zero

/-- `1 + εY` has determinant one exactly when `tr Y = 0`. -/
theorem det_one_add_epsilonMatrix_eq_one_iff (Y : Matrix n n A) :
    (1 + epsilonMatrix Y).det = 1 ↔ Y.trace = 0 := by
  rw [det_one_add_epsilonMatrix, add_eq_left]
  exact ⟨fun h => TrivSqZeroExt.inr_injective (h.trans (TrivSqZeroExt.inr_zero A).symm),
    fun h => h ▸ TrivSqZeroExt.inr_zero A⟩

end DualNumber

/-! ### Affine points -/

section AffinePoints

variable {R : CommRingCat.{u}}

/-- On affine points, the inclusion into `GL_n` is the inclusion of matrices. -/
theorem affinePointsEquiv_inclusion (S : CommAlgCat.{u} R)
    (f : (algSpec R).obj (op S) ⟶ (groupScheme n R).X) :
    GeneralLinear.affinePointsEquiv n R S (f ≫ (inclusion n R).hom.hom) =
      Matrix.SpecialLinearGroup.toGL (affinePointsEquiv n R S f) :=
  Corepresented.groupSchemeMap_affinePoints _ _ _ f

end AffinePoints

/-! ### Lie coordinates -/

section Lie

open GeneralLinear.DualNumber

variable {R : CommRingCat.{u}} {A : Type u} [CommRing A] [Algebra R A]

/-- The matrix coordinates of the Lie algebra of `SL_n`, through the inclusion into `GL_n`
and the published coordinates of the Lie algebra of `GL_n`. -/
def lieMatrix : Additive (lieKernel (groupScheme n R) A) →ₗ[A] Matrix n n A :=
  SpecialLinear.lieMatrix (n := n) (R := R) (A := A)

theorem pointKernelLinearEquiv_lieMatrix (X : Additive (lieKernel (groupScheme n R) A)) :
    pointKernelLinearEquiv (lieMatrix X) = Lie.targetMapLinear (inclusion n R) A X :=
  LinearEquiv.apply_symm_apply _ _

/-- The inclusion of `SL_n` into `GL_n` is a monomorphism of schemes. -/
instance mono_inclusion : Mono (inclusion n R).hom.hom := by
  constructor
  intro Z g h hgh
  apply (pointsEquiv n R Z).injective
  have h1 := congrArg (GeneralLinear.pointsEquiv n R Z) hgh
  rw [pointsEquiv_inclusion, pointsEquiv_inclusion] at h1
  apply Subtype.ext
  exact congrArg (fun g : GL n Γ(Z.left, ⊤) => g.val) h1

theorem lieMatrix_injective :
    Function.Injective (lieMatrix (n := n) (R := R) (A := A)) :=
  (pointKernelLinearEquiv (n := n) (R := R) (A := A)).symm.injective.comp
    (Lie.targetMapLinear_injective (inclusion n R) A)

/-- The affine dual-number matrix of an element of the Lie kernel of `SL_n` is `1 + εY` for
its coordinate matrix `Y`. -/
theorem affinePointsEquiv_lieKernel (X : Additive (lieKernel (groupScheme n R) A)) :
    ((affinePointsEquiv n R (CommAlgCat.of R (DualNumber A)) X.toMul.val :
        Matrix.SpecialLinearGroup n (DualNumber A)) : Matrix n n (DualNumber A)) =
      1 + epsilonMatrix (lieMatrix X) := by
  have h1 := pointKernelLinearEquiv_lieMatrix X
  have h2 := congrArg (fun x : Additive (lieKernel (GeneralLinear.groupScheme n R) A) =>
    GeneralLinear.affinePointsEquiv n R (CommAlgCat.of R (DualNumber A)) x.toMul.val) h1
  simp only [pointKernelLinearEquiv_toMul, pointKernelEquiv_val, lieKernelHomLinear_val] at h2
  have h4 := affinePointsEquiv_inclusion (n := n) (R := R) (CommAlgCat.of R (DualNumber A))
    X.toMul.val
  have h5 := pointUnit_matrix (R := R) (lieMatrix X)
  have h6 := h4.symm.trans (h2.symm.trans h5)
  exact congrArg (fun g : GL n (DualNumber A) => g.val) h6

/-- The Lie algebra of `SL_n` consists of trace-zero matrices. -/
theorem trace_lieMatrix (X : Additive (lieKernel (groupScheme n R) A)) :
    (lieMatrix X).trace = 0 := by
  rw [← det_one_add_epsilonMatrix_eq_one_iff, ← affinePointsEquiv_lieKernel]
  exact (affinePointsEquiv n R (CommAlgCat.of R (DualNumber A)) X.toMul.val).property

/-- Conversely every trace-zero matrix is the coordinate matrix of an element of the Lie
algebra of `SL_n`. -/
theorem exists_lieMatrix_eq (Y : Matrix n n A) (hY : Y.trace = 0) :
    ∃ X : Additive (lieKernel (groupScheme n R) A), lieMatrix X = Y := by
  let g : Matrix.SpecialLinearGroup n (DualNumber A) :=
    ⟨1 + epsilonMatrix Y, (det_one_add_epsilonMatrix_eq_one_iff Y).mpr hY⟩
  let p := (affinePointsEquiv n R (CommAlgCat.of R (DualNumber A))).symm g
  have hp : p ≫ (inclusion n R).hom.hom = (pointUnit Y : GeneralLinear.DualNumber.AffinePoints
      n R (DualNumber A)) := by
    apply (GeneralLinear.affinePointsEquiv n R (CommAlgCat.of R (DualNumber A))).injective
    rw [affinePointsEquiv_inclusion, pointUnit_matrix]
    apply Units.ext
    change ((affinePointsEquiv n R _ p : Matrix.SpecialLinearGroup n (DualNumber A)) :
      Matrix n n (DualNumber A)) = 1 + epsilonMatrix Y
    rw [MulEquiv.apply_symm_apply]
  have hred : Lie.reduction (groupScheme n R) p = 1 := by
    apply (cancel_mono (inclusion n R).hom.hom).mp
    rw [MonObj.one_comp]
    have h : Lie.reduction (groupScheme n R) p ≫ (inclusion n R).hom.hom =
        Lie.reduction (GeneralLinear.groupScheme n R) (p ≫ (inclusion n R).hom.hom) :=
      Category.assoc _ _ _
    rw [h, hp]
    exact pointReduction_pointUnit Y
  refine ⟨Additive.ofMul ⟨p, hred⟩, ?_⟩
  apply (pointKernelLinearEquiv (n := n) (R := R) (A := A)).injective
  rw [pointKernelLinearEquiv_lieMatrix]
  apply Additive.toMul.injective
  apply Subtype.ext
  exact hp

end Lie

end Langlands.GroupScheme.SpecialLinear.FinSucc
