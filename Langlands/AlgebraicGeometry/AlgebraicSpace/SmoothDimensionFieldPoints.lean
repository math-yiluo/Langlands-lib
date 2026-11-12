import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothDimensionRestrictions
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints

/-! # Actual field points in the finite dimension decomposition -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothTargetPointDimensions

variable {C : Type u} [CommRing C]
  {X Y : AlgebraicSpace (Spec (CommRingCat.of C))} {f : X ⟶ Y}
  (d : SmoothTargetPointDimensions f)
  {κ : Type u} [Field κ] [Algebra C κ]

/-- The unique occurring dimension selected by an actual field-valued point. -/
def fieldPointIndex (x : RingPoints C Y κ) : d.Index :=
  ⟨d.dimension (chartPointMap (uliftYonedaEquiv.symm x)
    (IsLocalRing.closedPoint κ)), ⟨_, rfl⟩⟩

/-- The original section itself factors through its actual open dimension stratum. -/
def fieldPointFactor (x : RingPoints C Y κ) :
    RingPoints C (d.targetSpace (d.fieldPointIndex x).val) κ := by
  refine ⟨x, ?_⟩
  intro t
  change d.dimension (chartPointMap (uliftYonedaEquiv.symm x) t) =
    d.dimension (chartPointMap (uliftYonedaEquiv.symm x) (IsLocalRing.closedPoint κ))
  rw [Subsingleton.elim t (IsLocalRing.closedPoint κ)]

@[simp]
theorem fieldPointFactor_map (x : RingPoints C Y κ) :
    RingPoints.map (d.targetInclusion (d.fieldPointIndex x).val)
      (d.fieldPointFactor x) = x := rfl

/-- Any factorization of a field point must have this same dimension index. -/
theorem fieldPointIndex_eq {n : d.Index}
    (y : RingPoints C (d.targetSpace n.val) κ) (x : RingPoints C Y κ)
    (hy : RingPoints.map (d.targetInclusion n.val) y = x) :
    n = d.fieldPointIndex x := by
  apply Subtype.ext
  have h := y.property (IsLocalRing.closedPoint κ)
  change d.dimension (chartPointMap (uliftYonedaEquiv.symm
    (RingPoints.map (d.targetInclusion n.val) y)) (IsLocalRing.closedPoint κ)) = n.val at h
  rw [hy] at h
  exact h.symm

/-- A field-valued point factors through exactly one member of the finite family. -/
theorem existsUnique_fieldPointFactor (x : RingPoints C Y κ) :
    ∃! n : d.Index, ∃ y : RingPoints C (d.targetSpace n.val) κ,
      RingPoints.map (d.targetInclusion n.val) y = x := by
  refine ⟨d.fieldPointIndex x, ⟨d.fieldPointFactor x, rfl⟩, ?_⟩
  rintro n ⟨y, hy⟩
  exact d.fieldPointIndex_eq y x hy

/-- Surjectivity on every occurring stratum gives surjectivity on original field points. -/
theorem surjective_fieldPoints_of_restrictions
    (hs : ∀ n : d.Index, Function.Surjective
      (RingPoints.map (d.restrictedMap n.val) :
        RingPoints C (d.sourceSpace n.val) κ → RingPoints C (d.targetSpace n.val) κ)) :
    Function.Surjective (RingPoints.map f : RingPoints C X κ → RingPoints C Y κ) := by
  intro x
  obtain ⟨y, hy⟩ := hs (d.fieldPointIndex x) (d.fieldPointFactor x)
  refine ⟨RingPoints.map (d.sourceInclusion (d.fieldPointIndex x).val) y, ?_⟩
  change (RingPoints.map (d.restrictedMap (d.fieldPointIndex x).val) y).val = x
  exact congrArg Subtype.val hy

end Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothTargetPointDimensions
