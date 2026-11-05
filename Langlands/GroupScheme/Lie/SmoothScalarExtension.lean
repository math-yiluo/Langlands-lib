import Langlands.GroupScheme.Lie.SmoothFiniteProjective
import Mathlib.LinearAlgebra.Contraction

/-! # Scalar extension of the actual smooth affine Lie module -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Lie

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
  [IsAffineHom G.X.hom] (A : Type u) [CommRing A] [Algebra R A]

attribute [local instance] coordinateOriginAlgebra

local instance coordinateOriginBaseScalarTower :
    IsScalarTower (coordinateAlgebra G) R A :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The universal cotangent property at the actual identity, with values
in any test algebra. -/
def identityCotangentHomEquiv :
    (identityCotangent G →ₗ[R] A) ≃ₗ[A] IdentityDerivation G (A := A) where
  toEquiv := ((LinearMap.liftBaseChangeEquiv R).symm.trans
    ((KaehlerDifferential.linearMapEquivDerivation R
      (coordinateAlgebra G)).restrictScalars R)).toEquiv
  map_add' f g := by
    ext c
    rfl
  map_smul' a f := by
    ext c
    rfl

@[simp]
theorem identityCotangentHomEquiv_apply (f : identityCotangent G →ₗ[R] A)
    (c : coordinateAlgebra G) :
    identityCotangentHomEquiv G A f c =
      f (1 ⊗ₜ KaehlerDifferential.D R (coordinateAlgebra G) c) := rfl

@[simp]
theorem identityCotangentDualEquiv_symm_apply
    (d : IdentityDerivation G (A := R)) (c : coordinateAlgebra G) :
    (identityCotangentDualEquiv G).symm d
      (1 ⊗ₜ KaehlerDifferential.D R (coordinateAlgebra G) c) = d c :=
  congrArg (fun e : IdentityDerivation G (A := R) => e c)
    ((identityCotangentDualEquiv G).apply_symm_apply d)

/-- The actual coefficient inclusion is linear for the coordinate-origin action. -/
def smoothOriginBaseLinear : R →ₗ[coordinateAlgebra G] A where
  toFun := algebraMap R A
  map_add' := map_add _
  map_smul' c r := by
    change algebraMap R A (coordinateOrigin G c * r) =
      algebraMap R A (coordinateOrigin G c) * algebraMap R A r
    exact map_mul _ _ _

/-- Extend an actual identity derivation by the test-algebra coefficient map. -/
def smoothIdentityDerivationBaseMap :
    IdentityDerivation G (A := R) →ₗ[R] IdentityDerivation G (A := A) :=
  (smoothOriginBaseLinear G A).compDer.restrictScalars R

/-- The natural tensor map on actual identity derivations over any ring. -/
def smoothIdentityDerivationTensorMap :
    A ⊗[R] IdentityDerivation G (A := R) →ₗ[A] IdentityDerivation G (A := A) :=
  (smoothIdentityDerivationBaseMap G A).liftBaseChange A

@[simp]
theorem smoothIdentityDerivationTensorMap_tmul (a : A)
    (d : IdentityDerivation G (A := R)) (c : coordinateAlgebra G) :
    smoothIdentityDerivationTensorMap G A (a ⊗ₜ d) c =
      a * algebraMap R A (d c) := rfl

variable [Smooth G.X.hom]

/-- Finite projectivity of the actual identity cotangent module makes the
natural derivation tensor map bijective for every test algebra. -/
theorem smoothIdentityDerivationTensorMap_bijective :
    Function.Bijective (smoothIdentityDerivationTensorMap G A) := by
  let e : A ⊗[R] IdentityDerivation G (A := R) ≃ₗ[R]
      IdentityDerivation G (A := A) :=
    (TensorProduct.congr (LinearEquiv.refl R A) (identityCotangentDualEquiv G).symm).trans
      ((TensorProduct.comm R A _).trans
        ((dualTensorHomEquiv R (identityCotangent G) A).trans
          ((identityCotangentHomEquiv G A).restrictScalars R)))
  have he : e.toLinearMap = (smoothIdentityDerivationTensorMap G A).restrictScalars R := by
    apply TensorProduct.ext'
    intro a d
    apply Derivation.ext
    intro c
    change identityCotangentHomEquiv G A
      (dualTensorHomEquiv R (identityCotangent G) A
        ((identityCotangentDualEquiv G).symm d ⊗ₜ a)) c =
      a * algebraMap R A (d c)
    rw [identityCotangentHomEquiv_apply, dualTensorHomEquiv_tmul,
      identityCotangentDualEquiv_symm_apply, Algebra.smul_def, mul_comm]
  rw [← LinearMap.coe_restrictScalars R, ← he]
  exact e.bijective

/-- Actual identity derivations of a smooth affine group commute with
arbitrary test-algebra scalar extension over any base ring. -/
def smoothIdentityDerivationScalarExtension :
    A ⊗[R] IdentityDerivation G (A := R) ≃ₗ[A] IdentityDerivation G (A := A) :=
  LinearEquiv.ofBijective (smoothIdentityDerivationTensorMap G A)
    (smoothIdentityDerivationTensorMap_bijective G A)

/-- The actual smooth affine dual-number Lie module commutes with
arbitrary test-algebra scalar extension over any base ring. -/
def smoothKernelScalarExtension :
    A ⊗[R] Additive (lieKernel G R) ≃ₗ[A] Additive (lieKernel G A) :=
  ((kernelDerivationLinearEquiv G (A := R)).baseChange R A _ _).trans
    ((smoothIdentityDerivationScalarExtension G A).trans
      (kernelDerivationLinearEquiv G (A := A)).symm)

@[simp]
theorem smoothKernelScalarExtension_tmul (a : A) (X : Additive (lieKernel G R)) :
    smoothKernelScalarExtension G A (a ⊗ₜ X) =
      a • lieKernelMapLinear G (Algebra.ofId R A) X := by
  apply (kernelDerivationLinearEquiv G (A := A)).injective
  apply Derivation.ext
  intro c
  simp only [smoothKernelScalarExtension, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, LinearEquiv.apply_symm_apply,
    smoothIdentityDerivationScalarExtension, LinearEquiv.ofBijective_apply, map_smul]
  change a * algebraMap R A (kernelDerivationEquiv G X.toMul c) =
    a * kernelDerivationEquiv G
      (lieKernelMap G (Algebra.ofId R A) X.toMul) c
  rw [kernelDerivationEquiv_naturality]
  rfl

end Langlands.GroupScheme.Lie
