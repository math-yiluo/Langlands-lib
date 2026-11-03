import Langlands.GroupScheme.Lie.ScalarExtension
import Langlands.GroupScheme.Lie.FiniteAction
import Langlands.GroupScheme.Lie.FiniteDimensional

/-! # Natural finite coordinates from actual Lie scalar extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

attribute [local instance] coordinateOriginAlgebra

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

omit [LocallyOfFiniteType G.X.hom] in
/-- Coefficient change of a base Lie vector agrees with its direct image. -/
theorem lieKernelMapLinear_base (f : A →ₐ[k] B) (x : Additive (lieKernel G k)) :
    lieKernelMapLinear G f (lieKernelMapLinear G (Algebra.ofId k A) x) =
      lieKernelMapLinear G (Algebra.ofId k B) x := by
  apply (kernelDerivationLinearEquiv G (A := B)).injective
  apply Derivation.ext
  intro c
  change kernelDerivationEquiv G
      (lieKernelMap G f (lieKernelMap G (Algebra.ofId k A) x.toMul)) c =
    kernelDerivationEquiv G (lieKernelMap G (Algebra.ofId k B) x.toMul) c
  rw [kernelDerivationEquiv_naturality, kernelDerivationEquiv_naturality,
    kernelDerivationEquiv_naturality]
  exact f.commutes _

/-- The actual kernel scalar-extension equivalence is natural in the test algebra. -/
theorem kernelScalarExtension_naturality (f : A →ₐ[k] B)
    (x : A ⊗[k] Additive (lieKernel G k)) :
    lieKernelMapLinear G f (kernelScalarExtension G A x) =
      kernelScalarExtension G B
        (TensorProduct.map f.toLinearMap (LinearMap.id : Module.End k _) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      kernelScalarExtension_tmul, LinearMap.map_smulₛₗ, lieKernelMapLinear_base]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Scalar extension intertwines the adjoint actions of base-field points. -/
theorem kernelScalarExtension_adjoint (g : AffinePoints G k)
    (x : A ⊗[k] Additive (lieKernel G k)) :
    adjoint G A (affineMap G (Algebra.ofId k A) g) (kernelScalarExtension G A x) =
      kernelScalarExtension G A ((adjoint G k g).baseChange A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [LinearMap.baseChange_tmul, kernelScalarExtension_tmul,
      LinearMap.map_smul, ← adjoint_naturality]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {d : ℕ}

/-- A finite basis of the base Lie kernel gives natural coordinates on every test algebra. -/
def finiteCoordinatesOfBasis
    (b : Module.Basis (Fin d) k (Additive (lieKernel G k))) :
    FiniteCoordinates G d where
  equiv A := (kernelScalarExtension G A).symm.trans (b.baseChange A).equivFun
  naturality {A B} f x := by
    obtain ⟨y, rfl⟩ := (kernelScalarExtension G A).surjective x
    rw [kernelScalarExtension_naturality]
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    induction y using TensorProduct.inductionOn with
    | tmul a x =>
      funext j
      simp only [TensorProduct.map_tmul, LinearMap.id_apply,
        Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul]
      exact (f.hom.toLinearMap.map_smul _ _).symm
    | add x y hx hy =>
      funext j
      simp only [map_add, hx, hy, Pi.add_apply]

/-- Natural finite coordinates for any affine locally finite-type group over a field. -/
def finiteCoordinates :
    FiniteCoordinates G (Module.finrank k (Additive (lieKernel G k))) :=
  finiteCoordinatesOfBasis G (Module.finBasis k _)

end Langlands.GroupScheme.Lie
