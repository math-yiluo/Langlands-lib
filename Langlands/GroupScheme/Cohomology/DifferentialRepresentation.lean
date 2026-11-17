import Langlands.GroupScheme.Cohomology.RegularCochains
import Langlands.GroupScheme.Lie.ActionDifferential
import Langlands.GroupScheme.Lie.SmoothScalarExtension

/-! # Quasi-coherent module representations from actual smooth affine actions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cohomology

variable {R : CommRingCat.{u}} {H U : GroupScheme (Spec R)}
variable [IsAffineHom U.X.hom] [Smooth U.X.hom]

attribute [local instance] Lie.coordinateOriginAlgebra

/-- The actual smooth affine Lie-module comparison is natural in arbitrary
affine test algebras. -/
theorem smoothKernelScalarExtension_naturality {A B : CommAlgCat.{u} R}
    (f : A ⟶ B) (x : ModulePoints (Additive (lieKernel U R)) A) :
    Lie.smoothKernelScalarExtension U B
        (modulePointMap (Additive (lieKernel U R)) f x) =
      lieKernelMapLinear U f.hom (Lie.smoothKernelScalarExtension U A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a X =>
    rw [modulePointMap_tmul, Lie.smoothKernelScalarExtension_tmul,
      Lie.smoothKernelScalarExtension_tmul]
    apply (Lie.kernelDerivationLinearEquiv U (A := B)).injective
    rw [(Lie.kernelDerivationLinearEquiv U (A := B)).map_smul]
    apply Derivation.ext
    intro b
    change f.hom a *
        Lie.kernelDerivationEquiv U (lieKernelMap U (Algebra.ofId R B) X.toMul) b =
      Lie.kernelDerivationEquiv U
        (lieKernelMap U f.hom
          (lieKernelScale U a (lieKernelMap U (Algebra.ofId R A) X.toMul))) b
    rw [Lie.kernelDerivationEquiv_naturality, Lie.kernelDerivationEquiv_naturality,
      Lie.kernelDerivationEquiv_scale]
    change f.hom a * (Algebra.ofId R B) (Lie.kernelDerivationEquiv U X.toMul b) =
      f.hom (a * Lie.kernelDerivationEquiv U
        (lieKernelMap U (Algebra.ofId R A) X.toMul) b)
    rw [Lie.kernelDerivationEquiv_naturality]
    simp only [Algebra.ofId_apply, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Transfer the differential action to the tensor extension of the actual
base Lie module. -/
def differentialTensorAction (a : AutomorphicAction H U) (A : CommAlgCat.{u} R) :
    H.affinePoints A →*
      (ModulePoints (Additive (lieKernel U R)) A ≃ₗ[A]
        ModulePoints (Additive (lieKernel U R)) A) where
  toFun h :=
    (Lie.smoothKernelScalarExtension U A).trans
      ((a.differentialRepresentation A h).trans
        (Lie.smoothKernelScalarExtension U A).symm)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    simp only [map_one, LinearEquiv.trans_apply]
    exact (Lie.smoothKernelScalarExtension U A).symm_apply_apply x
  map_mul' h k := by
    apply LinearEquiv.ext
    intro x
    simp only [map_mul, LinearEquiv.trans_apply, LinearEquiv.mul_apply,
      LinearEquiv.apply_symm_apply]

/-- Differentiating an actual action on a smooth affine group yields a natural
quasi-coherent module representation on its actual base Lie module. -/
def differentialModuleRepresentation (a : AutomorphicAction H U) :
    ModuleRepresentation (Additive (lieKernel U R)) H where
  action A := differentialTensorAction a A
  naturality {A B} f h x := by
    change modulePointMap (Additive (lieKernel U R)) f
        ((Lie.smoothKernelScalarExtension U A).symm
          (a.differential h (Lie.smoothKernelScalarExtension U A x))) =
      (Lie.smoothKernelScalarExtension U B).symm
        (a.differential (H.affinePointMap f h)
          (Lie.smoothKernelScalarExtension U B
            (modulePointMap (Additive (lieKernel U R)) f x)))
    apply (Lie.smoothKernelScalarExtension U B).injective
    change Lie.smoothKernelScalarExtension U B
        (modulePointMap (Additive (lieKernel U R)) f
          ((Lie.smoothKernelScalarExtension U A).symm
            (a.differential h (Lie.smoothKernelScalarExtension U A x)))) =
      Lie.smoothKernelScalarExtension U B
        ((Lie.smoothKernelScalarExtension U B).symm
          (a.differential (H.affinePointMap f h)
            (Lie.smoothKernelScalarExtension U B
              (modulePointMap (Additive (lieKernel U R)) f x))))
    rw [smoothKernelScalarExtension_naturality,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      a.differential_naturality, ← smoothKernelScalarExtension_naturality]
    rfl

/-- Conjugation gives the actual quasi-coherent adjoint representation. -/
def adjointModuleRepresentation (G : GroupScheme (Spec R))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] :
    ModuleRepresentation (Additive (lieKernel G R)) G :=
  differentialModuleRepresentation (AutomorphicAction.conjugation (𝟙 G))

end Langlands.GroupScheme.Cohomology
