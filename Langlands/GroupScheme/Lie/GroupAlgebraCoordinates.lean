import Langlands.GroupScheme.Lie.AffineCoordinates
import Langlands.GroupScheme.Lie.DerivationFinsupp
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! # Group-algebra coefficients of actual Lie kernels -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]

/-- The chosen affine coordinates are finite type when the original group is. -/
instance coordinateAlgebraFiniteType [LocallyOfFiniteType G.X.hom] :
    Algebra.FiniteType R (coordinateAlgebra G) := by
  have h : LocallyOfFiniteType ((algSpec R).obj (op (coordinateAlgebra G))).hom := by
    have h' : LocallyOfFiniteType ((coordinateIso G).hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using h'
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
    (algebraMap R (coordinateAlgebra G)))) at h
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  change RingHom.FiniteType (algebraMap R (coordinateAlgebra G)) at h
  exact RingHom.finiteType_algebraMap.mp h

attribute [local instance] coordinateOriginAlgebra

variable (M : Type u) [AddCommMonoid M]

local instance originGroupAlgebraModule :
    Module (coordinateAlgebra G) (AddMonoidAlgebra R M) :=
  (coordinateOriginAlgebra G (A := AddMonoidAlgebra R M)).toModule

/-- Coefficients are linear also for the coordinate-algebra action through the identity. -/
def originCoefficientLinearEquiv :
    AddMonoidAlgebra R M ≃ₗ[coordinateAlgebra G] (M →₀ R) where
  toEquiv := AddMonoidAlgebra.coeffAddEquiv.toEquiv
  map_add' _ _ := rfl
  map_smul' c x := by
    ext m
    change (AddMonoidAlgebra.single 0 (coordinateOrigin G c) * x).coeff m =
      coordinateOrigin G c * x.coeff m
    exact AddMonoidAlgebra.coeff_single_zero_mul _ _ _

@[simp] theorem originCoefficientLinearEquiv_apply (x : AddMonoidAlgebra R M) :
    originCoefficientLinearEquiv G M x = x.coeff := rfl

/-- Restrict the test-algebra module structure to the base ring. -/
instance kernelBaseModule : Module R (Additive (lieKernel G (AddMonoidAlgebra R M))) :=
  Module.restrictScalars R (AddMonoidAlgebra R M) _

instance kernelBaseScalarTower :
    IsScalarTower R (AddMonoidAlgebra R M)
      (Additive (lieKernel G (AddMonoidAlgebra R M))) :=
  IsScalarTower.restrictScalars R (AddMonoidAlgebra R M) _

/-- The actual Lie kernel over a group algebra has a finite family of base coefficients. -/
def kernelGroupAlgebraCoefficients [LocallyOfFiniteType G.X.hom] :
    Additive (lieKernel G (AddMonoidAlgebra R M)) ≃ₗ[R]
      (M →₀ Additive (lieKernel G R)) where
  toEquiv :=
    (kernelDerivationLinearEquiv G (A := AddMonoidAlgebra R M)).toEquiv.trans
      (((originCoefficientLinearEquiv G M).compDer.toEquiv).trans
        (derivationFinsuppLinearEquiv.toEquiv.trans
          (Finsupp.mapRange.linearEquiv
            (kernelDerivationLinearEquiv G (A := R)).symm).toEquiv))
  map_add' x y := by
    apply Finsupp.ext
    intro m
    apply (kernelDerivationLinearEquiv G (A := R)).injective
    ext c
    simp [derivationFinsuppLinearEquiv]
  map_smul' c x := by
    apply Finsupp.ext
    intro m
    apply (kernelDerivationLinearEquiv G (A := R)).injective
    ext z
    simp [derivationFinsuppLinearEquiv]
    change (((kernelDerivationLinearEquiv G)
      ((algebraMap R (AddMonoidAlgebra R M) c) • x)) z).coeff m = _
    rw [map_smul]
    change (AddMonoidAlgebra.single 0 c *
      (kernelDerivationLinearEquiv G x z)).coeff m = _
    exact AddMonoidAlgebra.coeff_single_zero_mul _ _ _

@[simp] theorem kernelGroupAlgebraCoefficients_apply
    [LocallyOfFiniteType G.X.hom]
    (x : Additive (lieKernel G (AddMonoidAlgebra R M))) (m : M)
    (c : coordinateAlgebra G) :
    kernelDerivationLinearEquiv G (kernelGroupAlgebraCoefficients G M x m) c =
      (kernelDerivationLinearEquiv G x c).coeff m := by
  simp [kernelGroupAlgebraCoefficients, derivationFinsuppLinearEquiv]

end Langlands.GroupScheme.Lie
