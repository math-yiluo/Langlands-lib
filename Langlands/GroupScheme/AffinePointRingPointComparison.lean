import Langlands.GroupScheme.AffinePointFiniteCoordinates

/-! # Actual group points and the general affine-scheme point carrier -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
variable (A : CommAlgCat.{u} R)

/-- The existing categorical point group, exposed through the named `RingPoint`
carrier. This is the group law on relative morphisms, without any transport. -/
abbrev ringPointGroup : Group (RingPoint R G.X A) :=
  inferInstanceAs (Group (ringTest R A ⟶ G.X))

local instance : Group (RingPoint R G.X A) := G.ringPointGroup A

/-- The identity identification of the two actual relative morphism carriers.
The multiplication on both sides is the existing group-object point law. -/
def affinePointsRingPointMulEquiv : G.affinePoints A ≃* RingPoint R G.X A where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem affinePointsRingPointMulEquiv_apply (x : G.affinePoints A) :
    G.affinePointsRingPointMulEquiv A x = (x : RingPoint R G.X A) := rfl

@[simp] theorem affinePointsRingPointMulEquiv_symm_apply (x : RingPoint R G.X A) :
    (G.affinePointsRingPointMulEquiv A).symm x = (x : G.affinePoints A) := rfl

variable [IsAffine G.X.left] [TopologicalSpace A]

/-- The actual group-point evaluation topology agrees, by the identity on points,
with the published general affine-scheme evaluation topology. -/
def affinePointsRingPointHomeomorph : G.affinePoints A ≃ₜ RingPoint R G.X A :=
  (G.affinePointsAlgebraHomeomorph A).trans
    (affineSchemePointHomeomorph R G.X A).symm

@[simp] theorem affinePointsRingPointHomeomorph_apply (x : G.affinePoints A) :
    G.affinePointsRingPointHomeomorph A x = (x : RingPoint R G.X A) := by
  exact (affineSchemePointEquiv R G.X A).symm_apply_apply x

@[simp] theorem affinePointsRingPointHomeomorph_symm_apply (x : RingPoint R G.X A) :
    (G.affinePointsRingPointHomeomorph A).symm x = (x : G.affinePoints A) := by
  exact (affineSchemePointEquiv R G.X A).symm_apply_apply x

@[simp] theorem affinePointsRingPointHomeomorph_evaluation (x : G.affinePoints A)
    (a : AffineCoordinateRing R G.X) :
    affineSchemePointEquiv R G.X A (G.affinePointsRingPointHomeomorph A x) a =
      G.affinePointEvaluation A x a := by
  rw [affinePointsRingPointHomeomorph_apply]
  exact G.affineSchemePointEquiv_evaluation A x a

@[simp] theorem affinePointsRingPointHomeomorph_mul (x y : G.affinePoints A) :
    G.affinePointsRingPointHomeomorph A (x * y) =
      G.affinePointsRingPointHomeomorph A x * G.affinePointsRingPointHomeomorph A y := by
  simp only [affinePointsRingPointHomeomorph_apply]
  rfl

@[simp] theorem affinePointsRingPointHomeomorph_inv (x : G.affinePoints A) :
    G.affinePointsRingPointHomeomorph A x⁻¹ =
      (G.affinePointsRingPointHomeomorph A x)⁻¹ := by
  simp only [affinePointsRingPointHomeomorph_apply]
  rfl

@[simp] theorem affinePointsRingPointHomeomorph_postcomp
    {H : GroupScheme (Spec R)} [IsAffine H.X.left] (f : G.X ⟶ H.X)
    (x : G.affinePoints A) :
    H.affinePointsRingPointHomeomorph A (x ≫ f) =
      G.affinePointsRingPointHomeomorph A x ≫ f := by
  simp only [affinePointsRingPointHomeomorph_apply]
  rfl

end Langlands.GroupScheme
