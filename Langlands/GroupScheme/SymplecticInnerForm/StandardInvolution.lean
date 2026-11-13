import Langlands.GroupScheme.SymplecticInnerForm.AdjointMatrix
import Langlands.GroupScheme.Quaternionic.Involution

/-! # The standard symplectic involution and the adjoint algebra action -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SymplecticInnerForm

open Quaternionic

variable (R : Type u) [CommRing R] (n : Type) [Fintype n] [DecidableEq n]

/-- The involution adjoint to the standard alternating form. -/
def standardInvolution : FirstKindInvolution R (Matrix (n ⊕ n) (n ⊕ n) R) where
  toLinearMap :=
    { toFun := fun x => -(Matrix.J n R * x.transpose * Matrix.J n R)
      map_add' := fun x y => by simp [Matrix.transpose_add, mul_add, add_mul, add_comm]
      map_smul' := fun r x => by simp [Matrix.transpose_smul] }
  map_one' := by
    change -(Matrix.J n R * (1 : Matrix (n ⊕ n) (n ⊕ n) R).transpose * Matrix.J n R) = 1
    simp [Matrix.J_squared]
  map_mul' := fun x y => by
    change -(Matrix.J n R * (x * y).transpose * Matrix.J n R) =
      (-(Matrix.J n R * y.transpose * Matrix.J n R)) *
        (-(Matrix.J n R * x.transpose * Matrix.J n R))
    simp only [Matrix.transpose_mul, neg_mul_neg]
    simp only [mul_assoc]
    rw [← mul_assoc (Matrix.J n R) (Matrix.J n R), Matrix.J_squared]
    simp
  involutive' := fun x => by
    change -(Matrix.J n R * (-(Matrix.J n R * x.transpose * Matrix.J n R)).transpose *
      Matrix.J n R) = x
    simp only [Matrix.transpose_neg, Matrix.transpose_mul, Matrix.J_transpose,
      Matrix.transpose_transpose, mul_neg, neg_neg]
    simp only [mul_assoc]
    simp only [Matrix.J_squared, mul_neg, neg_mul, neg_neg, mul_one]
    rw [← mul_assoc, Matrix.J_squared]
    simp

theorem standardInvolution_apply (x : Matrix (n ⊕ n) (n ⊕ n) R) :
    standardInvolution R n x = -(Matrix.J n R * x.transpose * Matrix.J n R) := rfl

theorem standardInvolution_mul_J (x : Matrix (n ⊕ n) (n ⊕ n) R) :
    standardInvolution R n x * Matrix.J n R = Matrix.J n R * x.transpose := by
  rw [standardInvolution_apply, neg_mul, mul_assoc, Matrix.J_squared]
  simp

theorem standardInvolution_symplectic (g : Matrix.symplecticGroup n R) :
    standardInvolution R n g = ((g⁻¹ : Matrix.symplecticGroup n R) :
      Matrix (n ⊕ n) (n ⊕ n) R) := by
  simp only [standardInvolution_apply, SymplecticGroup.coe_inv, neg_mul]

variable {R n}

theorem standardInvolution_map {S : Type u} [CommRing S] (f : R →+* S)
    (x : Matrix (n ⊕ n) (n ⊕ n) R) :
    (standardInvolution R n x).map f = standardInvolution S n (x.map f) := by
  change f.mapMatrix (-(Matrix.J n R * x.transpose * Matrix.J n R)) = _
  rw [map_neg, map_mul, map_mul]
  simp only [RingHom.mapMatrix_apply, Matrix.map_J, Matrix.transpose_map,
    standardInvolution_apply]

variable {K : Type u} [Field K] {M A : GroupScheme (Spec (CommRingCat.of K))}
  {q : M ⟶ A}

/-- The algebra action commutes with the standard symplectic involution. -/
theorem adjointMatrixHom_standardInvolution (hq : IsAdjointQuotient q)
    (i : M ≅ SymplecticMatrix.groupScheme n (CommRingCat.of K))
    {L : Type u} [CommRing L] [Algebra K L]
    (c : SpecialLinearInnerForm.matrixTest (K := K) L ⟶ A.X)
    (x : Matrix (n ⊕ n) (n ⊕ n) L) :
    adjointMatrixHom hq i c (standardInvolution L n x) =
      standardInvolution L n (adjointMatrixHom hq i c x) := by
  have h :
      (adjointMatrixHom hq i c).toLinearMap.comp (standardInvolution L n).toLinearMap =
      (standardInvolution L n).toLinearMap.comp (adjointMatrixHom hq i c).toLinearMap := by
    apply linearMap_ext_symplectic
    intro g
    obtain ⟨y, rfl⟩ := (affineMatrix i L).surjective g
    change adjointMatrixHom hq i c (standardInvolution L n (affineMatrix i L y)) =
      standardInvolution L n (adjointMatrixHom hq i c (affineMatrix i L y))
    rw [standardInvolution_symplectic, ← map_inv (affineMatrix i L),
      adjointMatrixHom_symplectic, adjointMatrixHom_symplectic,
      standardInvolution_symplectic, hq.innerAction.act_inv, map_inv]
  exact LinearMap.congr_fun h x

end Langlands.GroupScheme.SymplecticInnerForm
