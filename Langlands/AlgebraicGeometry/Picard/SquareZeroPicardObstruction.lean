import Langlands.AlgebraicGeometry.Picard.UnitH1Pullback

/-! # Actual Picard lifting over nonsplit square-zero immersions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.SquareZeroPicardObstruction

open SquareZeroUnitCohomology

variable {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
  (i : Y ⟶ X) [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥)

/-- The actual unit-sequence obstruction of a Picard class, in actual ideal-module H². -/
def obstructionMap : Group Y →+ idealCohomology i 2 :=
  (boundaryMap i hi 1).comp (Group.unitCohomologyAddEquiv Y).toAddMonoidHom

/-- The actual `1+a` cohomology map, expressed in the existing scheme Picard group. -/
def oneAddPicardMap : idealCohomology i 1 →+ Group X :=
  (Group.unitCohomologyAddEquiv X).symm.toAddMonoidHom.comp (oneAddMap i hi 1)

omit [CompactSpace Y] in
@[simp] lemma cohomology_oneAddPicardMap (a : idealCohomology i 1) :
    Group.unitCohomologyAddEquiv X (oneAddPicardMap i hi a) = oneAddMap i hi 1 a :=
  (Group.unitCohomologyAddEquiv X).apply_symm_apply _

private lemma cohomology_pullback (x : Group X) :
    Group.unitCohomologyAddEquiv Y (Group.pullback i x) =
      reductionMap i hi 1 (Group.unitCohomologyAddEquiv X x) :=
  Group.unitCohomologyClass_pullback_squareZero i hi x

/-- Exactness at the actual ambient Picard group. -/
theorem oneAddPicardMap_range_iff (x : Group X) :
    (∃ a : idealCohomology i 1, oneAddPicardMap i hi a = x) ↔
      Group.pullback i x = 0 := by
  calc
    _ ↔ ∃ a : idealCohomology i 1,
        oneAddMap i hi 1 a = Group.unitCohomologyAddEquiv X x := by
      apply exists_congr
      intro a
      rw [← cohomology_oneAddPicardMap i hi a]
      exact (Group.unitCohomologyAddEquiv X).injective.eq_iff.symm
    _ ↔ reductionMap i hi 1 (Group.unitCohomologyAddEquiv X x) = 0 :=
      oneAddMap_range_iff i hi 1 _
    _ ↔ Group.pullback i x = 0 := by
      rw [← cohomology_pullback i hi x]
      constructor
      · intro h
        exact (Group.unitCohomologyAddEquiv Y).injective
          (h.trans (map_zero _).symm)
      · intro h
        rw [h, map_zero]

omit [CompactSpace Y] in
/-- The ambiguity of `1+a` is precisely the actual degree-zero unit boundary. -/
theorem oneAddPicardMap_eq_zero_iff (a : idealCohomology i 1) :
    oneAddPicardMap i hi a = 0 ↔
      ∃ v : unitCohomology Y 0, boundaryMap i hi 0 v = a := by
  rw [boundaryMap_range_iff i hi 0 a, ← cohomology_oneAddPicardMap i hi a]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact (Group.unitCohomologyAddEquiv X).injective (h.trans (map_zero _).symm)

/-- An actual Picard class lifts exactly when its actual ideal-module H² obstruction vanishes. -/
theorem picard_lift_iff (y : Group Y) :
    (∃ x : Group X, Group.pullback i x = y) ↔ obstructionMap i hi y = 0 := by
  calc
    _ ↔ ∃ a : unitCohomology X 1,
        reductionMap i hi 1 a = Group.unitCohomologyAddEquiv Y y := by
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨Group.unitCohomologyAddEquiv X x,
          (cohomology_pullback i hi x).symm.trans
            (congrArg (Group.unitCohomologyAddEquiv Y) hx)⟩
      · rintro ⟨a, ha⟩
        refine ⟨(Group.unitCohomologyAddEquiv X).symm a,
          (Group.unitCohomologyAddEquiv Y).injective ?_⟩
        rw [cohomology_pullback, AddEquiv.apply_symm_apply]
        exact ha
    _ ↔ boundaryMap i hi 1 (Group.unitCohomologyAddEquiv Y y) = 0 :=
      h1_lift_iff i hi _
    _ ↔ obstructionMap i hi y = 0 := Iff.rfl

/-- An actual locally free rank-one module sheaf lifts up to actual module-sheaf isomorphism
precisely when its Picard obstruction vanishes. -/
theorem lineBundle_lift_iff (L : LineBundle Y) :
    (∃ M : LineBundle X, Nonempty (((LineBundle.pullback i).obj M).obj ≅ L.obj)) ↔
      obstructionMap i hi L.classOf = 0 := by
  rw [← picard_lift_iff i hi L.classOf]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M.classOf, ?_⟩
    rw [Group.pullback_lineBundle_classOf]
    exact (LineBundle.classOf_eq_iff _ _).mpr hM
  · rintro ⟨x, hx⟩
    refine ⟨Group.lineBundleRepresentative X x, (LineBundle.classOf_eq_iff _ _).mp ?_⟩
    rw [← Group.pullback_lineBundle_classOf, Group.classOf_lineBundleRepresentative, hx]

/-- Two ambient Picard classes have the same pullback precisely when their difference
comes from actual ideal-module H¹. -/
theorem same_pullback_iff (x x' : Group X) :
    Group.pullback i x = Group.pullback i x' ↔
      ∃ a : idealCohomology i 1, oneAddPicardMap i hi a + x = x' := by
  calc
    _ ↔ Group.pullback i (x' - x) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact eq_comm
    _ ↔ ∃ a : idealCohomology i 1, oneAddPicardMap i hi a = x' - x :=
      (oneAddPicardMap_range_iff i hi (x' - x)).symm
    _ ↔ _ := by
      apply exists_congr
      intro a
      exact eq_sub_iff_add_eq

omit [CompactSpace Y] in
/-- Ideal H¹ parameters give the same shifted Picard class precisely when their
difference is an actual degree-zero unit boundary. -/
theorem shifts_eq_iff (x : Group X) (a b : idealCohomology i 1) :
    oneAddPicardMap i hi a + x = oneAddPicardMap i hi b + x ↔
      ∃ v : unitCohomology Y 0, boundaryMap i hi 0 v = a - b := by
  rw [add_right_cancel_iff, ← sub_eq_zero, ← map_sub]
  exact oneAddPicardMap_eq_zero_iff i hi (a - b)

include hi in
/-- Vanishing of actual ideal-module H² suffices for surjectivity of actual Picard pullback. -/
theorem pullback_surjective_of_h2_zero
    (h : ∀ a : idealCohomology i 2, a = 0) : Function.Surjective (Group.pullback i) := by
  intro y
  exact (picard_lift_iff i hi y).mpr (h _)

include hi in
/-- Vanishing of actual ideal-module H¹ suffices for injectivity of actual Picard pullback. -/
theorem pullback_injective_of_h1_zero
    (h : ∀ a : idealCohomology i 1, a = 0) : Function.Injective (Group.pullback i) := by
  intro x x' hxx'
  obtain ⟨a, ha⟩ := (same_pullback_iff i hi x x').mp hxx'
  simpa only [h a, map_zero, zero_add] using ha

end Langlands.AlgebraicGeometry.Picard.SquareZeroPicardObstruction
