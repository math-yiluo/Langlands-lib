import Langlands.AlgebraicGeometry.Picard.UnitH1PullbackComposition
import Langlands.AlgebraicGeometry.Picard.SquareZeroPicardObstruction

/-! # Intrinsic naturality of actual square-zero Picard obstructions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.SquareZeroPicardObstructionNaturality

open SquareZeroUnitCohomology SquareZeroUnitNaturality SquareZeroPicardObstruction

variable {X Y Z : Scheme.{u}} [CompactSpace Y] [CompactSpace Z]
  (i : Y ⟶ X) (j : Z ⟶ Y)
  [IsClosedImmersion i] [IsClosedImmersion (j ≫ i)] [IsClosedImmersion j]
  (hi : i.ker ^ 2 = ⊥) (hji : (j ≫ i).ker ^ 2 = ⊥)
  (hj : IsNilpotent j.ker)

include hi hji hj

/-- Actual Picard obstruction commutes with intrinsic pullback to the inner scheme. -/
lemma obstructionMap_naturality (y : Group Y) :
    obstructionMap (j ≫ i) hji (Group.pullback j y) =
      idealCohomologyMap i j 2 (obstructionMap i hi y) := by
  change boundaryMap (j ≫ i) hji 1
      (Group.unitCohomologyAddEquiv Z (Group.pullback j y)) =
    idealCohomologyMap i j 2
      (boundaryMap i hi 1 (Group.unitCohomologyAddEquiv Y y))
  rw [Group.unitCohomologyAddEquiv_pullback j hj]
  exact boundaryMap_cohomologyMap i j hi hji hj 1 _

/-- Homomorphism form of intrinsic naturality for actual Picard obstructions. -/
lemma obstructionMap_comp_pullback :
    (obstructionMap (j ≫ i) hji).comp (Group.pullback j) =
      (idealCohomologyMap i j 2).comp (obstructionMap i hi) := by
  ext y
  exact obstructionMap_naturality i j hi hji hj y

/-- Further intrinsic pullback preserves vanishing of the actual obstruction. -/
lemma obstructionMap_pullback_eq_zero (y : Group Y) (hy : obstructionMap i hi y = 0) :
    obstructionMap (j ≫ i) hji (Group.pullback j y) = 0 := by
  rw [obstructionMap_naturality i j hi hji hj, hy, map_zero]

/-- Actual Picard pullback restricted to the kernels of the actual obstruction maps. -/
def obstructionKernelMap :
    (obstructionMap i hi).ker →+ (obstructionMap (j ≫ i) hji).ker where
  toFun y := ⟨Group.pullback j y.val,
    obstructionMap_pullback_eq_zero i j hi hji hj y.val y.property⟩
  map_zero' := Subtype.ext (map_zero (Group.pullback j))
  map_add' y y' := Subtype.ext (map_add (Group.pullback j) y.val y'.val)

@[simp]
lemma coe_obstructionKernelMap (y : (obstructionMap i hi).ker) :
    (obstructionKernelMap i j hi hji hj y : Group Z) = Group.pullback j y.val := rfl

/-- If the ideal H² map is injective, further pullback reflects obstruction vanishing. -/
lemma obstructionMap_pullback_eq_zero_iff
    (h : Function.Injective (idealCohomologyMap i j 2)) (y : Group Y) :
    obstructionMap (j ≫ i) hji (Group.pullback j y) = 0 ↔
      obstructionMap i hi y = 0 := by
  rw [obstructionMap_naturality i j hi hji hj]
  exact h.eq_iff' (map_zero _)

variable [CompactSpace X]

/-- Under injectivity on ideal H², further pullback reflects actual Picard liftability. -/
lemma picard_lift_further_pullback_iff
    (h : Function.Injective (idealCohomologyMap i j 2)) (y : Group Y) :
    (∃ x : Group X, Group.pullback (j ≫ i) x = Group.pullback j y) ↔
      ∃ x : Group X, Group.pullback i x = y := by
  rw [picard_lift_iff (j ≫ i) hji, picard_lift_iff i hi]
  exact obstructionMap_pullback_eq_zero_iff i j hi hji hj h y

end Langlands.AlgebraicGeometry.Picard.SquareZeroPicardObstructionNaturality
