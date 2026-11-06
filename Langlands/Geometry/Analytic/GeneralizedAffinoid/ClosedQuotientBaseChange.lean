import Langlands.Geometry.Analytic.GeneralizedAffinoid.ClosedQuotient
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteDomainIdealDescent

/-! # Actual closed quotients commute with bounded affinoid base change -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.ClosedQuotient

open AffinoidPushout

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K A B)
  (J : Ideal A) [IsClosed (J : Set A)]

local instance : IsClosed (f.closedIdealMap J : Set B) :=
  f.isClosed_closedIdealMap J

omit [CompleteSpace K] [IsClosed (J : Set A)] in
/-- The quotient map to the changed closed ideal annihilates the original ideal. -/
theorem changedMap_annihilates (a : A) (ha : a ∈ J) :
    (map B (f.closedIdealMap J)).comp f a = 0 :=
  (map_eq_zero_iff B (f.closedIdealMap J) (f a)).mpr (f.mem_closedIdealMap ha)

/-- The first quotient leg into the quotient by the closed extended ideal. -/
def changedQuotientMap :
    BoundedAlgHom K (algebra A J) (algebra B (f.closedIdealMap J)) :=
  lift A J ((map B (f.closedIdealMap J)).comp f) (changedMap_annihilates f J)

/-- The map from the actual affinoid pushout to the quotient by the
closed extended ideal retains both original quotient maps. -/
def pushoutToChangedQuotient :
    BoundedAlgHom K (AffinoidPushout.algebra (map A J) f)
      (algebra B (f.closedIdealMap J)) :=
  AffinoidPushout.lift (map A J) f _ (changedQuotientMap f J)
    (map B (f.closedIdealMap J)) (lift_comp_map A J _ _)

theorem pushoutToChangedQuotient_comp_rightMap :
    (pushoutToChangedQuotient f J).comp (rightMap (map A J) f) =
      map B (f.closedIdealMap J) :=
  lift_comp_rightMap _ _ _ _ _ _

omit [CompleteSpace K] in
/-- The actual second pushout leg annihilates the entire closed extended ideal. -/
theorem rightMap_annihilates_closedIdealMap
    (b : B) (hb : b ∈ f.closedIdealMap J) :
    rightMap (map A J) f b = 0 := by
  have hclosed : IsClosed
      (RingHom.ker (rightMap (map A J) f).toAlgHom.toRingHom :
        Set B) :=
    isClosed_eq (rightMap (map A J) f).continuous continuous_const
  have hle : f.closedIdealMap J ≤
      RingHom.ker (rightMap (map A J) f).toAlgHom.toRingHom := by
    apply (f.closedIdealMap_le_iff _ _ hclosed).mpr
    intro a ha
    change rightMap (map A J) f (f a) = 0
    have h := congrArg
      (fun h : BoundedAlgHom K A (AffinoidPushout.algebra (map A J) f) => h a)
      (condition (map A J) f)
    change leftMap (map A J) f (map A J a) = rightMap (map A J) f (f a) at h
    rw [(map_eq_zero_iff A J a).mpr ha, map_zero] at h
    exact h.symm
  exact hle hb

/-- Bounded quotient descent constructs the inverse map, including its bound. -/
def changedQuotientToPushout :
    BoundedAlgHom K (algebra B (f.closedIdealMap J))
      (AffinoidPushout.algebra (map A J) f) :=
  lift B (f.closedIdealMap J) (rightMap (map A J) f)
    (rightMap_annihilates_closedIdealMap f J)

omit [CompleteSpace K] in
theorem changedQuotientToPushout_comp_map :
    (changedQuotientToPushout f J).comp (map B (f.closedIdealMap J)) =
      rightMap (map A J) f :=
  lift_comp_map _ _ _ _

theorem changedQuotientToPushout_comp_pushoutToChangedQuotient :
    (changedQuotientToPushout f J).comp (pushoutToChangedQuotient f J) =
      BoundedAlgHom.id K (AffinoidPushout.algebra (map A J) f) := by
  have hr :
      ((changedQuotientToPushout f J).comp (pushoutToChangedQuotient f J)).comp
          (rightMap (map A J) f) = rightMap (map A J) f := by
    rw [BoundedAlgHom.comp_assoc, pushoutToChangedQuotient_comp_rightMap,
      changedQuotientToPushout_comp_map]
  apply AffinoidPushout.hom_ext (map A J) f _
  · apply hom_ext
    calc
      _ = ((changedQuotientToPushout f J).comp
          (pushoutToChangedQuotient f J)).comp
            ((leftMap (map A J) f).comp (map A J)) := rfl
      _ = ((changedQuotientToPushout f J).comp
          (pushoutToChangedQuotient f J)).comp
            ((rightMap (map A J) f).comp f) := by rw [condition]
      _ = (((changedQuotientToPushout f J).comp
          (pushoutToChangedQuotient f J)).comp (rightMap (map A J) f)).comp f := rfl
      _ = (rightMap (map A J) f).comp f := by rw [hr]
      _ = (leftMap (map A J) f).comp (map A J) := (condition _ _).symm
      _ = _ := rfl
  · exact hr

theorem pushoutToChangedQuotient_comp_changedQuotientToPushout :
    (pushoutToChangedQuotient f J).comp (changedQuotientToPushout f J) =
      BoundedAlgHom.id K (algebra B (f.closedIdealMap J)) := by
  apply hom_ext
  rw [BoundedAlgHom.comp_assoc, changedQuotientToPushout_comp_map,
    pushoutToChangedQuotient_comp_rightMap]
  rfl

/-- The two actual quotient constructions are boundedly equivalent without
assuming flatness, strict radii or a nontrivial coefficient valuation. -/
def pushoutEquiv :
    BoundedAlgEquiv K (AffinoidPushout.algebra (map A J) f)
      (algebra B (f.closedIdealMap J)) :=
  BoundedAlgEquiv.ofHomInv (pushoutToChangedQuotient f J) (changedQuotientToPushout f J)
    (fun x => congrArg (fun h => h x)
      (changedQuotientToPushout_comp_pushoutToChangedQuotient f J))
    (fun y => congrArg (fun h => h y)
      (pushoutToChangedQuotient_comp_changedQuotientToPushout f J))

/-- Base change of the quotient has exactly the closed extended kernel. -/
theorem ker_rightMap :
    RingHom.ker (rightMap (map A J) f).toAlgHom.toRingHom = f.closedIdealMap J := by
  ext b
  change rightMap (map A J) f b = 0 ↔ b ∈ f.closedIdealMap J
  rw [← map_eq_zero_iff B (f.closedIdealMap J) b]
  have h := congrArg
    (fun h : BoundedAlgHom K B (algebra B (f.closedIdealMap J)) => h b)
    (pushoutToChangedQuotient_comp_rightMap f J)
  constructor
  · intro hb
    change pushoutToChangedQuotient f J (rightMap (map A J) f b) = _ at h
    rw [hb, map_zero] at h
    exact h.symm
  · intro hb
    apply (pushoutEquiv f J).toAlgEquiv.injective
    change pushoutToChangedQuotient f J (rightMap (map A J) f b) =
      pushoutToChangedQuotient f J 0
    rw [map_zero]
    exact h.trans hb

/-- The actual base-changed quotient leg is admissible with its stored norm. -/
theorem rightMap_isAdmissibleEpi :
    (rightMap (map A J) f).IsAdmissibleEpi := by
  rw [← changedQuotientToPushout_comp_map]
  apply BoundedAlgHom.IsAdmissibleEpi.comp
    (map B (f.closedIdealMap J)) (changedQuotientToPushout f J)
  · exact map_isAdmissibleEpi _ _
  · exact BoundedAlgHom.isAdmissibleEpi_of_bounded_section _
      (pushoutToChangedQuotient f J)
      (changedQuotientToPushout_comp_pushoutToChangedQuotient f J)

end Langlands.Analytic.PresentedAffinoidAlgebra.ClosedQuotient
