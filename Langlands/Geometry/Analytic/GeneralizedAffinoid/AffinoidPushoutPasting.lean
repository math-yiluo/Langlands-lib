import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushout
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # Pasting actual bounded affinoid pushouts -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C D : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C) (h : BoundedAlgHom K C D)

/-- The old pushout maps to the direct changed-base pushout by both
original bounded legs. -/
def pastingInnerMap : BoundedAlgHom K (algebra f g) (algebra f (h.comp g)) :=
  lift f g _ (leftMap f (h.comp g)) ((rightMap f (h.comp g)).comp h)
    (by rw [BoundedAlgHom.comp_assoc, condition])

theorem pastingInnerMap_comp_left :
    (pastingInnerMap f g h).comp (leftMap f g) = leftMap f (h.comp g) :=
  lift_comp_leftMap _ _ _ _ _ _

theorem pastingInnerMap_comp_right :
    (pastingInnerMap f g h).comp (rightMap f g) = (rightMap f (h.comp g)).comp h :=
  lift_comp_rightMap _ _ _ _ _ _

/-- The full iterated closed quotient maps to the full direct quotient. -/
def pastingToDirect :
    BoundedAlgHom K (algebra (rightMap f g) h) (algebra f (h.comp g)) :=
  lift (rightMap f g) h _ (pastingInnerMap f g h) (rightMap f (h.comp g))
    (pastingInnerMap_comp_right f g h)

theorem pastingToDirect_comp_left :
    (pastingToDirect f g h).comp (leftMap (rightMap f g) h) = pastingInnerMap f g h :=
  lift_comp_leftMap _ _ _ _ _ _

theorem pastingToDirect_comp_right :
    (pastingToDirect f g h).comp (rightMap (rightMap f g) h) = rightMap f (h.comp g) :=
  lift_comp_rightMap _ _ _ _ _ _

omit [CompleteSpace K] in
private theorem directToPasting_condition :
    ((leftMap (rightMap f g) h).comp (leftMap f g)).comp f =
      (rightMap (rightMap f g) h).comp (h.comp g) := by
  rw [BoundedAlgHom.comp_assoc, condition, ← BoundedAlgHom.comp_assoc, condition,
    BoundedAlgHom.comp_assoc]

/-- The inverse full map is constructed by the direct pushout's actual
bounded universal property. -/
def directToPasting :
    BoundedAlgHom K (algebra f (h.comp g)) (algebra (rightMap f g) h) :=
  lift f (h.comp g) _ ((leftMap (rightMap f g) h).comp (leftMap f g))
    (rightMap (rightMap f g) h) (directToPasting_condition f g h)

theorem directToPasting_comp_left :
    (directToPasting f g h).comp (leftMap f (h.comp g)) =
      (leftMap (rightMap f g) h).comp (leftMap f g) :=
  lift_comp_leftMap _ _ _ _ _ _

theorem directToPasting_comp_right :
    (directToPasting f g h).comp (rightMap f (h.comp g)) = rightMap (rightMap f g) h :=
  lift_comp_rightMap _ _ _ _ _ _

theorem pastingToDirect_comp_directToPasting :
    (pastingToDirect f g h).comp (directToPasting f g h) =
      BoundedAlgHom.id K (algebra f (h.comp g)) := by
  apply hom_ext f (h.comp g)
  · rw [BoundedAlgHom.comp_assoc, directToPasting_comp_left,
      ← BoundedAlgHom.comp_assoc, pastingToDirect_comp_left,
      pastingInnerMap_comp_left, BoundedAlgHom.id_comp]
  · rw [BoundedAlgHom.comp_assoc, directToPasting_comp_right,
      pastingToDirect_comp_right, BoundedAlgHom.id_comp]

theorem directToPasting_comp_pastingToDirect :
    (directToPasting f g h).comp (pastingToDirect f g h) =
      BoundedAlgHom.id K (algebra (rightMap f g) h) := by
  apply hom_ext (rightMap f g) h
  · rw [BoundedAlgHom.comp_assoc, pastingToDirect_comp_left, BoundedAlgHom.id_comp]
    apply hom_ext f g
    · rw [BoundedAlgHom.comp_assoc, pastingInnerMap_comp_left, directToPasting_comp_left]
    · rw [BoundedAlgHom.comp_assoc, pastingInnerMap_comp_right,
        ← BoundedAlgHom.comp_assoc, directToPasting_comp_right, condition]
  · rw [BoundedAlgHom.comp_assoc, pastingToDirect_comp_right,
      directToPasting_comp_right, BoundedAlgHom.id_comp]

/-- Pasting two actual bounded affinoid pushouts gives an entire bounded
algebra equivalence, preserving the original changed-base leg. -/
def pastingEquiv :
    BoundedAlgEquiv K (algebra (rightMap f g) h) (algebra f (h.comp g)) :=
  BoundedAlgEquiv.ofHomInv (pastingToDirect f g h) (directToPasting f g h)
    (fun x => congrArg (fun q : BoundedAlgHom K (algebra (rightMap f g) h)
      (algebra (rightMap f g) h) => q x) (directToPasting_comp_pastingToDirect f g h))
    (fun x => congrArg (fun q : BoundedAlgHom K (algebra f (h.comp g))
      (algebra f (h.comp g)) => q x) (pastingToDirect_comp_directToPasting f g h))

theorem pastingEquiv_comp_right :
    (pastingEquiv f g h).toBoundedAlgHom.comp (rightMap (rightMap f g) h) =
      rightMap f (h.comp g) :=
  pastingToDirect_comp_right f g h

theorem pastingEquiv_comp_left :
    (pastingEquiv f g h).toBoundedAlgHom.comp
      ((leftMap (rightMap f g) h).comp (leftMap f g)) = leftMap f (h.comp g) := by
  change (pastingToDirect f g h).comp
    ((leftMap (rightMap f g) h).comp (leftMap f g)) = _
  rw [← BoundedAlgHom.comp_assoc, pastingToDirect_comp_left, pastingInnerMap_comp_left]

end Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout
