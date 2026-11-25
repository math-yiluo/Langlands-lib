import Langlands.GroupScheme.Lie.CounitDerivationBracket
import Langlands.GroupScheme.Rational.HopfCoordinateComparison
import Mathlib.Algebra.Lie.TransferInstance

/-! # The Lie bracket on actual affine group-scheme tangents -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry WithConv

namespace Langlands.GroupScheme.Lie

open AffineCoordinates

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] coordinateOriginAlgebra

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
    {A : Type u} [CommRing A] [Algebra R A]

private local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

local notation "B" => hopfAlgebra G
local notation "D" => coordinateAlgebra G
local notation "C" => WithConv (B →ₗ[R] A)
local notation "e" => lieCoordinateAlgEquiv G

private theorem convOne_eq_origin (b : B) :
    (1 : C) b = (algebraMap D A) (e b) := by
  change algebraMap R A (Bialgebra.counitAlgHom R B b) =
    algebraMap R A (coordinateOrigin G (e b))
  rw [lieCoordinateAlgEquiv_counit]

private def coordinateCounitDerivationEquiv :
    IdentityDerivation G (A := A) ≃ₗ[A] counitDerivationLie R B A where
  toFun d := ⟨toConv (d.toLinearMap.comp (e).toLinearMap), by
    change IsCounitDerivation (toConv (d.toLinearMap.comp (e).toLinearMap))
    intro x y
    change d (e (x * y)) = d (e x) * (1 : C) y + (1 : C) x * d (e y)
    rw [map_mul, d.leibniz, Algebra.smul_def, Algebra.smul_def,
      convOne_eq_origin G, convOne_eq_origin G, add_comm, mul_comm (d (e x))]⟩
  invFun f := Derivation.mk' (f.val.ofConv.comp (e).symm.toLinearMap) (by
    intro x y
    change f.val ((e).symm (x * y)) = x • f.val ((e).symm y) + y • f.val ((e).symm x)
    have hf : IsCounitDerivation f.val := f.property
    rw [map_mul, hf, convOne_eq_origin G, convOne_eq_origin G,
      AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, Algebra.smul_def, Algebra.smul_def,
      add_comm, mul_comm (f.val ((e).symm x))])
  left_inv d := by
    ext x
    change d (e ((e).symm x)) = d x
    rw [AlgEquiv.apply_symm_apply]
  right_inv f := by
    apply Subtype.ext
    apply ofConv_injective
    ext b
    change f.val ((e).symm (e b)) = f.val b
    rw [AlgEquiv.symm_apply_apply]
  map_add' d₁ d₂ := by
    apply Subtype.ext
    apply ofConv_injective
    ext b
    rfl
  map_smul' a d := by
    apply Subtype.ext
    apply ofConv_injective
    ext b
    rfl

/-- Actual dual-number kernel points, with their existing module structure, are
identified with the counit derivations of the Hopf coordinate algebra. -/
def kernelCounitDerivationLinearEquiv :
    Additive (lieKernel G A) ≃ₗ[A] counitDerivationLie R B A :=
  (kernelDerivationLinearEquiv G).trans (coordinateCounitDerivationEquiv G)

@[simp] theorem kernelCounitDerivationLinearEquiv_apply (x : Additive (lieKernel G A)) (b : B) :
    (kernelCounitDerivationLinearEquiv G x).val b =
      kernelDerivationLinearEquiv G x (e b) := rfl

/-- The Lie bracket on the original tangent module is the transported
convolution commutator. -/
instance instAffineKernelLieRing : LieRing (Additive (lieKernel G A)) :=
  (kernelCounitDerivationLinearEquiv G).toAddEquiv.lieRing

/-- The bracket is bilinear for the existing test-algebra scalar action. -/
instance instAffineKernelLieAlgebra : LieAlgebra A (Additive (lieKernel G A)) :=
  (kernelCounitDerivationLinearEquiv G (A := A)).lieAlgebra

/-- The tangent-to-counit-derivation comparison preserves the Lie bracket. -/
def kernelCounitDerivationLieEquiv :
    Additive (lieKernel G A) ≃ₗ⁅A⁆ counitDerivationLie R B A :=
  (kernelCounitDerivationLinearEquiv G).lieEquiv A

theorem kernelCounitDerivationLinearEquiv_lie (x y : Additive (lieKernel G A)) :
    (kernelCounitDerivationLinearEquiv G ⁅x, y⁆).val =
      (kernelCounitDerivationLinearEquiv G x).val * (kernelCounitDerivationLinearEquiv G y).val -
        (kernelCounitDerivationLinearEquiv G y).val * (kernelCounitDerivationLinearEquiv G x).val := by
  change (kernelCounitDerivationLieEquiv G ⁅x, y⁆).val = _
  rw [LieEquiv.map_lie]
  rfl

end Langlands.GroupScheme.Lie
