import Langlands.GroupScheme.Lie.SquareZeroKernelTensorAction
import Langlands.GroupScheme.Cohomology.RegularCochains
import Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor

/-! # Square-zero kernel coefficients on flat affine tests -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Lie.SquareZero

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]

/-- The image of an actual square-zero ideal remains square-zero under any
change of coefficient ring. -/
theorem extendedIdeal_square (I : Ideal R) (hI : I ^ 2 = ⊥)
    (B : CommAlgCat.{u} R) : (I.map (algebraMap R B)) ^ 2 = ⊥ := by
  rw [← Ideal.map_pow, hI, Ideal.map_bot]

omit [IsAffineHom G.X.hom] in
/-- Evaluation of a Lie vector in an ideal element commutes with every
compatible change of coefficient rings and ideals. -/
theorem tangentPoint_naturality
    {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (I : Ideal A) (J : Ideal B) (hI : I ^ 2 = ⊥) (hJ : J ^ 2 = ⊥)
    (f : A →ₐ[R] B) (i : I) (j : J) (hij : f i = j) (X : lieKernel G A) :
    affineMap G f (tangentPoint G I hI i X).val =
      (tangentPoint G J hJ j (lieKernelMap G f X)).val := by
  simp only [tangentPoint_val, lieKernelMap_val, ← affineMap_comp]
  have he : f.comp (tangentEvaluation (R := R) I hI i) =
      (tangentEvaluation (R := R) J hJ j).comp
        (GeneralLinear.DualNumber.coefficientAlgMap f) := by
    apply AlgHom.ext
    intro z
    simp only [AlgHom.comp_apply, tangentEvaluation_apply, map_add, map_mul, hij]
    rfl
  rw [he]

variable [Smooth G.X.hom]
variable (I : Ideal R) (hI : I ^ 2 = ⊥) (B : CommAlgCat.{u} R) [Module.Flat R B]

/-- For flat coefficient algebras, the actual reduction kernel has the natural
module tensor coefficients of the base ideal and base Lie module. -/
def flatKernelCoefficientEquiv :
    Additive (kernel G (I.map (algebraMap R B))) ≃+
      Cohomology.ModulePoints (I ⊗[R] Additive (lieKernel G R)) B :=
  (kernelTensorAddEquiv G (I.map (algebraMap R B)) (extendedIdeal_square I hI B)).trans
    (((TensorProduct.congr
      ((Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor.idealTensorEquiv
        (R := B) I).symm.restrictScalars R)
      (LinearEquiv.refl R (Additive (lieKernel G R)))).trans
        (TensorProduct.assoc R B I (Additive (lieKernel G R)))).toAddEquiv)

/-- The actual point belonging to a module coefficient on a flat affine test. -/
def flatKernelPoint
    (v : Cohomology.ModulePoints (I ⊗[R] Additive (lieKernel G R)) B) :
    AffinePoints G B :=
  ((flatKernelCoefficientEquiv G I hI B).symm v).toMul.val

@[simp]
theorem flatKernelPoint_add
    (v w : Cohomology.ModulePoints (I ⊗[R] Additive (lieKernel G R)) B) :
    flatKernelPoint G I hI B (v + w) =
      flatKernelPoint G I hI B v * flatKernelPoint G I hI B w := by
  simp only [flatKernelPoint, map_add, toMul_add]
  rfl

/-- The coefficient comparison is the actual tangent evaluation on pure
module tensors. -/
theorem flatKernelPoint_tmul (b : B) (i : I) (X : Additive (lieKernel G R)) :
    flatKernelPoint G I hI B (b ⊗ₜ[R] (i ⊗ₜ[R] X)) =
      (tangentPoint G (I.map (algebraMap R B)) (extendedIdeal_square I hI B)
        ((Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor.idealTensorEquiv
          (R := B) I) (b ⊗ₜ[R] i))
        (lieKernelMap G (Algebra.ofId R B) X.toMul)).val := by
  change ((kernelTensorAddEquiv G (I.map (algebraMap R B))
    (extendedIdeal_square I hI B)).symm
      (((Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor.idealTensorEquiv
        (R := B) I) (b ⊗ₜ[R] i)) ⊗ₜ[R] X)).toMul.val = _
  rw [kernelTensorAddEquiv_symm_tmul]
  rfl

attribute [local instance] coordinateOriginAlgebra

variable {B} {C : CommAlgCat.{u} R} [Module.Flat R C]

/-- Naturality of actual points reconstructed from the module coefficients,
on arbitrary morphisms between flat affine tests. -/
theorem flatKernelPoint_naturality (f : B ⟶ C)
    (v : Cohomology.ModulePoints (I ⊗[R] Additive (lieKernel G R)) B) :
    affineMap G f.hom (flatKernelPoint G I hI B v) =
      flatKernelPoint G I hI C
        (Cohomology.modulePointMap (I ⊗[R] Additive (lieKernel G R)) f v) := by
  induction v using TensorProduct.inductionOn with
  | tmul b t =>
    induction t using TensorProduct.inductionOn with
    | tmul i X =>
      rw [Cohomology.modulePointMap_tmul, flatKernelPoint_tmul, flatKernelPoint_tmul]
      have hi : f.hom
          ((Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor.idealTensorEquiv
            (R := B) I) (b ⊗ₜ[R] i) : B) =
          ((Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor.idealTensorEquiv
            (R := C) I) (f.hom b ⊗ₜ[R] i) : C) := by
        simp only [Langlands.AlgebraicGeometry.Deformation.ElementaryKernelTensor.idealTensorEquiv_tmul,
          map_mul, AlgHom.commutes]
      rw [tangentPoint_naturality G _ _ (extendedIdeal_square I hI B)
        (extendedIdeal_square I hI C) f.hom _ _ hi]
      congr 2
      apply (Lie.kernelDerivationEquiv G).injective
      apply Derivation.ext
      intro c
      rw [Lie.kernelDerivationEquiv_naturality, Lie.kernelDerivationEquiv_naturality,
        Lie.kernelDerivationEquiv_naturality]
      exact f.hom.commutes _
    | add t s ht hs =>
      simp only [TensorProduct.tmul_add, map_add, flatKernelPoint_add, map_mul, ht, hs]
  | add v w hv hw =>
    simp only [map_add, flatKernelPoint_add, map_mul, hv, hw]

/-- Every reconstructed coefficient point reduces to the actual identity. -/
theorem flatKernelPoint_reduction
    (v : Cohomology.ModulePoints (I ⊗[R] Additive (lieKernel G R)) B) :
    reduction G (I.map (algebraMap R B)) (flatKernelPoint G I hI B v) = 1 :=
  ((flatKernelCoefficientEquiv G I hI B).symm v).toMul.property

/-- The actual-point reconstruction remembers the entire module coefficient. -/
theorem flatKernelPoint_injective : Function.Injective (flatKernelPoint G I hI B) := by
  intro v w h
  apply (flatKernelCoefficientEquiv G I hI B).symm.injective
  apply Additive.toMul.injective
  exact Subtype.ext h

/-- Forward naturality of the coefficient comparison for any two compatible
actual kernel points on flat tests. -/
theorem flatKernelCoefficientEquiv_naturality (f : B ⟶ C)
    (x : kernel G (I.map (algebraMap R B)))
    (y : kernel G (I.map (algebraMap R C)))
    (hxy : affineMap G f.hom x.val = y.val) :
    flatKernelCoefficientEquiv G I hI C (Additive.ofMul y) =
      Cohomology.modulePointMap (I ⊗[R] Additive (lieKernel G R)) f
        (flatKernelCoefficientEquiv G I hI B (Additive.ofMul x)) := by
  apply (flatKernelCoefficientEquiv G I hI C).symm.injective
  rw [AddEquiv.symm_apply_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  change y.val = flatKernelPoint G I hI C _
  rw [← hxy]
  have hn := flatKernelPoint_naturality G I hI f
    (flatKernelCoefficientEquiv G I hI B (Additive.ofMul x))
  simpa only [flatKernelPoint, AddEquiv.symm_apply_apply,
    Additive.toMul, Equiv.symm_apply_apply] using hn

end Langlands.GroupScheme.Lie.SquareZero
