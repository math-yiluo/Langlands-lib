import Langlands.GroupScheme.Torus.FixedSubgroupSmoothAlgebraBridge
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Finite projectivity of the actual Lie module of a smooth affine group -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Lie

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
  [IsAffineHom G.X.hom]

attribute [local instance] coordinateOriginAlgebra

/-- The actual relative cotangent module pulled back to the identity point
through the coordinate augmentation. -/
abbrev identityCotangent :=
  R ⊗[coordinateAlgebra G] KaehlerDifferential R (coordinateAlgebra G)

/-- The dual of the identity cotangent module is the module of actual
coordinate derivations at the augmentation. -/
def identityCotangentDualEquiv :
    Module.Dual R (identityCotangent G) ≃ₗ[R] IdentityDerivation G (A := R) :=
  (LinearMap.liftBaseChangeEquiv R).symm.trans
    ((KaehlerDifferential.linearMapEquivDerivation R
      (coordinateAlgebra G)).restrictScalars R)

/-- The actual dual-number Lie kernel is the dual of the actual identity
cotangent module. -/
def kernelIdentityCotangentDualEquiv :
    Additive (lieKernel G R) ≃ₗ[R] Module.Dual R (identityCotangent G) :=
  (kernelDerivationLinearEquiv G).trans (identityCotangentDualEquiv G).symm

variable [Smooth G.X.hom]

/-- Smoothness makes the identity cotangent module finite. -/
instance finite_identityCotangent : Module.Finite R (identityCotangent G) := by
  let : Algebra.Smooth R (coordinateAlgebra G) :=
    Diagonalizable.FixedSubgroupSmoothAlgebraBridge.coordinateAlgebra_smooth G
  infer_instance

/-- Smoothness makes the identity cotangent module projective. -/
instance projective_identityCotangent : Module.Projective R (identityCotangent G) := by
  let : Algebra.Smooth R (coordinateAlgebra G) :=
    Diagonalizable.FixedSubgroupSmoothAlgebraBridge.coordinateAlgebra_smooth G
  infer_instance

/-- The actual Lie module of a smooth affine group over an arbitrary ring
is finite. -/
instance finite_lieKernel_of_smooth : Module.Finite R (Additive (lieKernel G R)) :=
  Module.Finite.equiv (kernelIdentityCotangentDualEquiv G).symm

/-- The actual Lie module of a smooth affine group over an arbitrary ring
is projective. -/
instance projective_lieKernel_of_smooth : Module.Projective R (Additive (lieKernel G R)) :=
  Module.Projective.of_equiv (kernelIdentityCotangentDualEquiv G).symm

end Langlands.GroupScheme.Lie
