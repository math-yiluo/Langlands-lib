import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Determinant transitions of bases adapted to a split surjection -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v w w' w''

namespace Langlands.LinearAlgebra.SplitBasis

variable {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type w} [AddCommGroup W] [Module R W]
    (f : V →ₗ[R] W) (s : W →ₗ[R] V) (hs : ∀ w, f (s w) = w)

/-- The projection to the actual kernel determined by a linear section. -/
def kernelProjection : V →ₗ[R] LinearMap.ker f :=
  (LinearMap.id - s.comp f).codRestrict _ (fun x => by
    change f (x - s (f x)) = 0
    rw [map_sub, hs, sub_self])

/-- The product decomposition associated with any specified linear right inverse. -/
def splitEquiv : V ≃ₗ[R] W × LinearMap.ker f where
  toLinearMap := f.prod (kernelProjection f s hs)
  invFun x := s x.1 + x.2.val
  left_inv x := by
    change s (f x) + (x - s (f x)) = x
    abel
  right_inv x := by
    have hx : f x.2.val = 0 := x.2.property
    apply Prod.ext
    · change f (s x.1 + x.2.val) = x.1
      rw [map_add, hs, hx, add_zero]
    · apply Subtype.ext
      change s x.1 + x.2.val - s (f (s x.1 + x.2.val)) = x.2.val
      rw [map_add, hs, hx, add_zero]
      abel

variable (t : W →ₗ[R] V) (ht : ∀ w, f (t w) = w)

/-- The difference of two sections takes values in the actual kernel. -/
def sectionDifference : W →ₗ[R] LinearMap.ker f :=
  (t - s).codRestrict _ (fun w => by
    change f (t w - s w) = 0
    rw [map_sub, ht, hs, sub_self])

theorem splitEquiv_apply_symm (x : W × LinearMap.ker f) :
    splitEquiv f s hs ((splitEquiv f t ht).symm x) =
      (x.1, sectionDifference f s hs t ht x.1 + x.2) := by
  have hx : f x.2.val = 0 := x.2.property
  apply Prod.ext
  · change f (t x.1 + x.2.val) = x.1
    rw [map_add, ht, hx, add_zero]
  · apply Subtype.ext
    change t x.1 + x.2.val - s (f (t x.1 + x.2.val)) =
      (t x.1 - s x.1) + x.2.val
    rw [map_add, ht, hx, add_zero]
    abel

variable {ι : Type w'} {κ : Type w''}

/-- A quotient basis and an actual kernel basis give a basis of the middle
module after choosing a linear section. -/
def adaptedBasis (b : Module.Basis ι R W) (c : Module.Basis κ R (LinearMap.ker f)) :
    Module.Basis (ι ⊕ κ) R V :=
  (b.prod c).map (splitEquiv f s hs).symm

/-- Changing sections affects only the lower-left block of an adapted basis transition. -/
theorem adaptedBasis_toMatrix
    (b b' : Module.Basis ι R W) (c c' : Module.Basis κ R (LinearMap.ker f)) :
    (adaptedBasis f s hs b c).toMatrix (adaptedBasis f t ht b' c') =
      Matrix.fromBlocks (b.toMatrix b') 0
        (Matrix.of (fun k i => c.repr (sectionDifference f s hs t ht (b' i)) k))
        (c.toMatrix c') := by
  ext i j
  rw [Module.Basis.toMatrix_apply]
  change (b.prod c).repr
      (splitEquiv f s hs ((splitEquiv f t ht).symm ((b'.prod c') j))) i = _
  rw [splitEquiv_apply_symm]
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks, Module.Basis.toMatrix_apply]

/-- The determinant transition is the product of quotient and kernel transitions,
independently of the two choices of linear section. -/
theorem adaptedBasis_toMatrix_det [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b b' : Module.Basis ι R W) (c c' : Module.Basis κ R (LinearMap.ker f)) :
    ((adaptedBasis f s hs b c).toMatrix (adaptedBasis f t ht b' c')).det =
      (b.toMatrix b').det * (c.toMatrix c').det := by
  rw [adaptedBasis_toMatrix, Matrix.det_fromBlocks_zero₁₂]

end Langlands.LinearAlgebra.SplitBasis
