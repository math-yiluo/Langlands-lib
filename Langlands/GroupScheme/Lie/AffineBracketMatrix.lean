import Langlands.GroupScheme.Lie.AffineBracketFunctoriality
import Langlands.GroupScheme.Lie.RepresentationDifferential
import Mathlib.Algebra.Lie.Matrix

/-! # Matrix comparisons for the affine tangent Lie bracket -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite WithConv
open scoped TensorProduct Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

open AffineCoordinates

attribute [local instance 100] LieRing.ofAssociativeRing

namespace MatrixRepresentation

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffineHom G.X.hom]
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

local notation "B" => hopfAlgebra G

private abbrev hopfMatrix : Matrix n n B :=
  (ρ.affineMatrix (algebra G) (pointEquiv G (algebra G) (𝟙 _)) : Matrix n n (algebra G))

private theorem affineMatrix_pointEquiv {S : CommAlgCat.{u} R} (f : algebra G ⟶ S) :
    (ρ.affineMatrix S (pointEquiv G S f) : Matrix n n S) = (hopfMatrix ρ).map f.hom := by
  have h := ρ.affineMatrix_naturality f (pointEquiv G (algebra G) (𝟙 _))
  rw [← pointEquiv_comp, Category.id_comp] at h
  exact congrArg Units.val h

set_option backward.isDefEq.respectTransparency false in
private theorem comul_hopfMatrix (i j : n) :
    Coalgebra.comul (R := R) (hopfMatrix ρ i j) =
      ∑ l, hopfMatrix ρ i l ⊗ₜ[R] hopfMatrix ρ l j := by
  let S : CommAlgCat R := CommAlgCat.of R (B ⊗[R] B)
  let L : B →ₐ[R] S := Algebra.TensorProduct.includeLeft
  let D : B →ₐ[R] S := Algebra.TensorProduct.includeRight
  have hprod : Algebra.TensorProduct.productMap L D = AlgHom.id R (B ⊗[R] B) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    change (a ⊗ₜ[R] (1 : B)) * ((1 : B) ⊗ₜ[R] b) = a ⊗ₜ[R] b
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  let c : algebra G ⟶ S := CommAlgCat.ofHom (Bialgebra.comulAlgHom R B)
  let l : algebra G ⟶ S := CommAlgCat.ofHom L
  let d : algebra G ⟶ S := CommAlgCat.ofHom D
  have h : pointEquiv G S c = pointEquiv G S l * pointEquiv G S d := by
    have hh := pointEquiv_hopf_mul G (C := S) L D
    rw [hprod, AlgHom.id_comp] at hh
    exact hh
  have hM : (ρ.affineMatrix S (pointEquiv G S c) : Matrix n n S) =
      (ρ.affineMatrix S (pointEquiv G S l) : Matrix n n S) *
        (ρ.affineMatrix S (pointEquiv G S d) : Matrix n n S) := by
    rw [h, map_mul, Units.val_mul]
  rw [affineMatrix_pointEquiv, affineMatrix_pointEquiv, affineMatrix_pointEquiv] at hM
  have hh := congrArg (fun M : Matrix n n S => M i j) hM
  rw [Matrix.map_apply, Matrix.mul_apply] at hh
  refine hh.trans (Finset.sum_congr rfl fun a _ => ?_)
  change (hopfMatrix ρ i a ⊗ₜ[R] (1 : B)) * ((1 : B) ⊗ₜ[R] hopfMatrix ρ a j) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

variable (A : Type u) [CommRing A] [Algebra R A]

set_option backward.isDefEq.respectTransparency false in
private theorem kernelDifferential_eq_hopfDerivation (x : Additive (lieKernel G A)) (i j : n) :
    ρ.kernelDifferential A x i j = (Lie.kernelCounitDerivationLinearEquiv G x).val (hopfMatrix ρ i j) := by
  rw [Lie.kernelCounitDerivationLinearEquiv_eq_snd]
  let S : CommAlgCat R := CommAlgCat.of R (DualNumber A)
  let f : algebra G ⟶ S := (pointEquiv G S).symm x.toMul.val
  have h := affineMatrix_pointEquiv ρ f
  change ρ.kernelDifferential A x i j = (f.hom (hopfMatrix ρ i j)).snd
  change (((ρ.affineMatrix S x.toMul.val : Matrix n n S) i j)).snd = _
  have hh := congrArg (fun M : Matrix n n S => (M i j).snd) h
  simpa only [f, Equiv.apply_symm_apply, Matrix.map_apply] using hh

private theorem convMul_apply_hopfMatrix (f g : WithConv (B →ₗ[R] A)) (i j : n) :
    (f * g) (hopfMatrix ρ i j) = ∑ l, f (hopfMatrix ρ i l) * g (hopfMatrix ρ l j) := by
  rw [LinearMap.convMul_apply, comul_hopfMatrix]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply]

/-- The differential of an actual matrix representation takes the tangent bracket
to the matrix commutator. -/
theorem kernelDifferential_commutator (x y : Additive (lieKernel G A)) :
    ρ.kernelDifferential A ⁅x, y⁆ =
      ρ.kernelDifferential A x * ρ.kernelDifferential A y -
        ρ.kernelDifferential A y * ρ.kernelDifferential A x := by
  apply Matrix.ext
  intro i j
  rw [kernelDifferential_eq_hopfDerivation, Lie.kernelCounitDerivationLinearEquiv_lie]
  simp only [ofConv_sub, LinearMap.sub_apply, convMul_apply_hopfMatrix, Matrix.sub_apply,
    Matrix.mul_apply, kernelDifferential_eq_hopfDerivation]

/-- The original matrix differential, now as a Lie algebra homomorphism. -/
def kernelDifferentialLieHom : Additive (lieKernel G A) →ₗ⁅A⁆ Matrix n n A :=
  { ρ.kernelDifferential A with map_lie' := fun {x y} => ρ.kernelDifferential_commutator A x y }

@[simp] theorem kernelDifferentialLieHom_toLinearMap :
    (ρ.kernelDifferentialLieHom A).toLinearMap = ρ.kernelDifferential A := rfl

end MatrixRepresentation

namespace GeneralLinear.DualNumber

variable {R : CommRingCat.{u}} {n : Type} [Fintype n] [DecidableEq n]
    {A : Type u} [CommRing A] [Algebra R A]

/-- The usual `1 + εX` comparison is an isomorphism of Lie algebras. -/
def pointKernelLieEquiv : Matrix n n A ≃ₗ⁅A⁆ Additive (lieKernel (groupScheme n R) A) := by
  let ρ : MatrixRepresentation (groupScheme n R) n := 𝟙 _
  have ht : Lie.targetMapLinear ρ A = LinearMap.id := by
    have h := Lie.targetMapLieHom_id (G := groupScheme n R) (A := A)
    exact congrArg LieHom.toLinearMap h
  have he (x : Additive (lieKernel (groupScheme n R) A)) :
      ρ.kernelDifferential A x = pointKernelLinearEquiv.symm x := by
    rw [MatrixRepresentation.kernelDifferential, ht]
    rfl
  exact (show Additive (lieKernel (groupScheme n R) A) ≃ₗ⁅A⁆ Matrix n n A from
    { pointKernelLinearEquiv.symm with
      map_lie' := fun {x y} => by
        change pointKernelLinearEquiv.symm ⁅x, y⁆ =
          ⁅pointKernelLinearEquiv.symm x, pointKernelLinearEquiv.symm y⁆
        rw [← he ⁅x, y⁆, ← he x, ← he y]
        exact ρ.kernelDifferential_commutator A x y }).symm

@[simp] theorem pointKernelLieEquiv_toLinearEquiv :
    (pointKernelLieEquiv (n := n) (R := R) (A := A)).toLinearEquiv = pointKernelLinearEquiv := rfl

end GeneralLinear.DualNumber

end Langlands.GroupScheme
