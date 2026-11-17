import Langlands.GroupScheme.Lie.SquareZeroKernelConjugation
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # The actual adjoint action on square-zero kernel tensors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Lie.SquareZero

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
variable {A : Type u} [CommRing A] [Algebra R A] (I : Ideal A)

attribute [local instance] coordinateOriginAlgebra

/-- Evaluation is balanced between the ideal element and the Lie vector. -/
theorem tangentPoint_smul (hI : I ^ 2 = ⊥) (i : I) (a : A)
    (X : Additive (lieKernel G A)) :
    tangentPoint G I hI i (a • X).toMul =
      tangentPoint G I hI (a • i) X.toMul := by
  apply (kernelDerivationEquiv G I hI).injective
  ext b
  rw [tangentPoint_derivation, tangentPoint_derivation]
  change Lie.kernelDerivationEquiv G (lieKernelScale G a X.toMul) b * (i : A) = _
  rw [Lie.kernelDerivationEquiv_scale]
  simp only [Derivation.smul_apply, smul_eq_mul, Submodule.coe_smul_of_tower]
  ring

attribute [local instance] coordinateOriginBaseScalarTower

@[simp]
theorem idealCotangentHomEquiv_apply
    (f : identityCotangent G →ₗ[R] I) (b : coordinateAlgebra G) :
    idealCotangentHomEquiv G I f b =
      f (1 ⊗ₜ KaehlerDifferential.D R (coordinateAlgebra G) b) := rfl

variable [Smooth G.X.hom]

/-- The inverse of the previously constructed base-Lie tensor comparison
on a pure tensor is actual tangent evaluation in that ideal element. -/
theorem kernelTensorAddEquiv_symm_tmul (hI : I ^ 2 = ⊥) (i : I)
    (X : Additive (lieKernel G R)) :
    (kernelTensorAddEquiv G I hI).symm (i ⊗ₜ[R] X) =
      Additive.ofMul (tangentPoint G I hI i
        (lieKernelMap G (Algebra.ofId R A) X.toMul)) := by
  apply (kernelAddEquiv G I hI).injective
  simp only [kernelTensorAddEquiv, AddEquiv.symm_trans_apply,
    AddEquiv.apply_symm_apply]
  apply Derivation.ext
  intro b
  apply Subtype.ext
  change (idealCotangentHomEquiv G I
      (dualTensorHomEquiv R (identityCotangent G) I
        ((kernelIdentityCotangentDualEquiv G) X ⊗ₜ[R] i)) b : A) = _
  rw [idealCotangentHomEquiv_apply, dualTensorHomEquiv_tmul]
  change (kernelIdentityCotangentDualEquiv G X
      (1 ⊗ₜ KaehlerDifferential.D R (coordinateAlgebra G) b)) • (i : A) = _
  change (identityCotangentDualEquiv G).symm
      (Lie.kernelDerivationLinearEquiv G X)
      (1 ⊗ₜ KaehlerDifferential.D R (coordinateAlgebra G) b) • (i : A) = _
  rw [identityCotangentDualEquiv_symm_apply]
  change (Lie.kernelDerivationEquiv G X.toMul b) • (i : A) =
    (kernelDerivationEquiv G I hI (tangentPoint G I hI i
      (lieKernelMap G (Algebra.ofId R A) X.toMul)) b : A)
  rw [Algebra.smul_def, tangentPoint_derivation, Lie.kernelDerivationEquiv_naturality]
  rfl

/-- Replace the base Lie tensor by the actual Lie module over the coefficient
algebra, using the canonical cancellation of scalar extension. -/
def idealLieBaseChange :
    (I ⊗[A] Additive (lieKernel G A)) ≃ₗ[R]
      (I ⊗[R] Additive (lieKernel G R)) :=
  ((TensorProduct.congr (LinearEquiv.refl A I)
    (smoothKernelScalarExtension G A).symm).restrictScalars R).trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R A A I
        (Additive (lieKernel G R))).restrictScalars R)

theorem idealLieBaseChange_tmul_extension (i : I)
    (z : A ⊗[R] Additive (lieKernel G R)) :
    idealLieBaseChange G I (i ⊗ₜ[A] smoothKernelScalarExtension G A z) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange R A A I
        (Additive (lieKernel G R)) (i ⊗ₜ[A] z) := by
  simp only [idealLieBaseChange, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, LinearEquiv.symm_apply_apply]

/-- Every actual square-zero kernel point is an ideal tensor with a vector in
the actual Lie module over the coefficient algebra. -/
def idealLieKernelEquiv (hI : I ^ 2 = ⊥) :
    (I ⊗[A] Additive (lieKernel G A)) ≃+ Additive (kernel G I) :=
  (idealLieBaseChange G I).toAddEquiv.trans (kernelTensorAddEquiv G I hI).symm

/-- The complete ideal-Lie equivalence has actual tangent evaluation as its
pure tensor formula. -/
theorem idealLieKernelEquiv_tmul (hI : I ^ 2 = ⊥) (i : I)
    (X : Additive (lieKernel G A)) :
    idealLieKernelEquiv G I hI (i ⊗ₜ[A] X) =
      Additive.ofMul (tangentPoint G I hI i X.toMul) := by
  obtain ⟨z, rfl⟩ := (smoothKernelScalarExtension G A).surjective X
  induction z using TensorProduct.inductionOn with
  | tmul a X =>
    change (kernelTensorAddEquiv G I hI).symm
      (idealLieBaseChange G I (i ⊗ₜ[A] smoothKernelScalarExtension G A (a ⊗ₜ[R] X))) = _
    rw [idealLieBaseChange_tmul_extension,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      kernelTensorAddEquiv_symm_tmul, smoothKernelScalarExtension_tmul,
      tangentPoint_smul]
    rfl
  | add z w hz hw =>
    simp only [map_add, TensorProduct.tmul_add, hz, hw,
      toMul_add, map_mul, ofMul_mul]

/-- Tensoring the actual adjoint endomorphism with the identity of the actual
ideal gives the action corresponding to point conjugation on the kernel. -/
theorem idealLieKernelEquiv_adjoint (hI : I ^ 2 = ⊥)
    (g : AffinePoints G A) (z : I ⊗[A] Additive (lieKernel G A)) :
    (idealLieKernelEquiv G I hI
      (TensorProduct.map (LinearMap.id : I →ₗ[A] I) (adjoint G A g) z)).toMul =
      kernelConjugation G I g (idealLieKernelEquiv G I hI z).toMul := by
  induction z using TensorProduct.inductionOn with
  | tmul i X =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply,
      idealLieKernelEquiv_tmul, idealLieKernelEquiv_tmul]
    exact tangentPoint_adjoint G I hI i g X
  | add z w hz hw =>
    simp only [map_add, toMul_add, map_mul, hz, hw]

end Langlands.GroupScheme.Lie.SquareZero
