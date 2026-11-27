import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidPushout
import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtension

/-! # Bounded affinoid pushouts commute with ground field extension -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  (L : Type v) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)

local notation "P" => AffinoidPushout.algebra f g
local notation "Q" => AffinoidPushout.algebra (map K L f) (map K L g)

private local instance : NormedAlgebra K Q := NormedAlgebra.restrictScalars K L Q

private local instance : IsScalarTower K L Q := IsScalarTower.of_algebraMap_eq' rfl

private theorem pushoutConditionOnIota :
    ((overBase K L (AffinoidPushout.leftMap (map K L f) (map K L g))).comp
      (iota K L B)).comp f =
    ((overBase K L (AffinoidPushout.rightMap (map K L f) (map K L g))).comp
      (iota K L C)).comp g := by
  apply BoundedAlgHom.ext
  intro a
  simpa only [BoundedAlgHom.comp_apply, overBase_apply, map_iota] using
    congrArg (fun h : BoundedAlgHom L (algebra K L A) Q => h (iota K L A a))
      (AffinoidPushout.condition (map K L f) (map K L g))

private def toPushout : BoundedAlgHom L (algebra K L P) Q :=
  lift K L P Q (AffinoidPushout.lift f g Q
    ((overBase K L (AffinoidPushout.leftMap (map K L f) (map K L g))).comp (iota K L B))
    ((overBase K L (AffinoidPushout.rightMap (map K L f) (map K L g))).comp (iota K L C))
    (pushoutConditionOnIota L f g))

private theorem toPushout_comp_leftMap :
    (toPushout L f g).comp (map K L (AffinoidPushout.leftMap f g)) =
      AffinoidPushout.leftMap (map K L f) (map K L g) := by
  apply hom_ext K L B
  apply BoundedAlgHom.ext
  intro b
  simpa only [toPushout, BoundedAlgHom.comp_apply, overBase_apply, map_iota, lift_iota] using
    congrArg (fun h : BoundedAlgHom K B Q => h b)
      (AffinoidPushout.lift_comp_leftMap f g Q _ _ (pushoutConditionOnIota L f g))

private theorem toPushout_comp_rightMap :
    (toPushout L f g).comp (map K L (AffinoidPushout.rightMap f g)) =
      AffinoidPushout.rightMap (map K L f) (map K L g) := by
  apply hom_ext K L C
  apply BoundedAlgHom.ext
  intro c
  simpa only [toPushout, BoundedAlgHom.comp_apply, overBase_apply, map_iota, lift_iota] using
    congrArg (fun h : BoundedAlgHom K C Q => h c)
      (AffinoidPushout.lift_comp_rightMap f g Q _ _ (pushoutConditionOnIota L f g))

private theorem mappedPushoutCondition :
    (map K L (AffinoidPushout.leftMap f g)).comp (map K L f) =
      (map K L (AffinoidPushout.rightMap f g)).comp (map K L g) := by
  rw [← map_comp, ← map_comp, AffinoidPushout.condition]

private def fromPushout : BoundedAlgHom L Q (algebra K L P) :=
  AffinoidPushout.lift (map K L f) (map K L g) (algebra K L P)
    (map K L (AffinoidPushout.leftMap f g)) (map K L (AffinoidPushout.rightMap f g))
    (mappedPushoutCondition L f g)

private theorem fromPushout_comp_leftMap :
    (fromPushout L f g).comp (AffinoidPushout.leftMap (map K L f) (map K L g)) =
      map K L (AffinoidPushout.leftMap f g) :=
  AffinoidPushout.lift_comp_leftMap _ _ _ _ _ (mappedPushoutCondition L f g)

private theorem fromPushout_comp_rightMap :
    (fromPushout L f g).comp (AffinoidPushout.rightMap (map K L f) (map K L g)) =
      map K L (AffinoidPushout.rightMap f g) :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _ (mappedPushoutCondition L f g)

private theorem extendedPushout_hom_ext {D : Type w} [NormedCommRing D]
    [NormedAlgebra L D] [NormedAlgebra K D] [IsScalarTower K L D]
    {α β : BoundedAlgHom L (algebra K L P) D}
    (hl : α.comp (map K L (AffinoidPushout.leftMap f g)) =
      β.comp (map K L (AffinoidPushout.leftMap f g)))
    (hr : α.comp (map K L (AffinoidPushout.rightMap f g)) =
      β.comp (map K L (AffinoidPushout.rightMap f g))) :
    α = β := by
  apply hom_ext K L P
  apply AffinoidPushout.hom_ext f g D
  · apply BoundedAlgHom.ext
    intro b
    simpa only [BoundedAlgHom.comp_apply, overBase_apply, map_iota] using
      congrArg (fun h : BoundedAlgHom L (algebra K L B) D => h (iota K L B b)) hl
  · apply BoundedAlgHom.ext
    intro c
    simpa only [BoundedAlgHom.comp_apply, overBase_apply, map_iota] using
      congrArg (fun h : BoundedAlgHom L (algebra K L C) D => h (iota K L C c)) hr

private theorem fromPushout_comp_toPushout :
    (fromPushout L f g).comp (toPushout L f g) = BoundedAlgHom.id L (algebra K L P) := by
  apply extendedPushout_hom_ext L f g
  · rw [BoundedAlgHom.comp_assoc, toPushout_comp_leftMap, fromPushout_comp_leftMap,
      BoundedAlgHom.id_comp]
  · rw [BoundedAlgHom.comp_assoc, toPushout_comp_rightMap, fromPushout_comp_rightMap,
      BoundedAlgHom.id_comp]

private theorem toPushout_comp_fromPushout :
    (toPushout L f g).comp (fromPushout L f g) = BoundedAlgHom.id L Q := by
  apply AffinoidPushout.hom_ext (map K L f) (map K L g) Q
  · rw [BoundedAlgHom.comp_assoc, fromPushout_comp_leftMap, toPushout_comp_leftMap,
      BoundedAlgHom.id_comp]
  · rw [BoundedAlgHom.comp_assoc, fromPushout_comp_rightMap, toPushout_comp_rightMap,
      BoundedAlgHom.id_comp]

private theorem fromPushout_toPushout (p : algebra K L P) :
    fromPushout L f g (toPushout L f g p) = p := by
  change ((fromPushout L f g).comp (toPushout L f g)) p = _
  rw [fromPushout_comp_toPushout, BoundedAlgHom.id_apply]

private theorem toPushout_fromPushout (q : Q) :
    toPushout L f g (fromPushout L f g q) = q := by
  change ((toPushout L f g).comp (fromPushout L f g)) q = _
  rw [toPushout_comp_fromPushout, BoundedAlgHom.id_apply]

/-- Extending the actual bounded pushout agrees with pushing out the extended
maps, compatibly with both bounded quotient legs. -/
def pushoutComparison : BoundedAlgEquiv L (algebra K L P) Q :=
  BoundedAlgEquiv.ofHomInv (toPushout L f g) (fromPushout L f g)
    (fromPushout_toPushout L f g) (toPushout_fromPushout L f g)

@[simp]
theorem pushoutComparison_comp_leftMap :
    (pushoutComparison L f g).toBoundedAlgHom.comp (map K L (AffinoidPushout.leftMap f g)) =
      AffinoidPushout.leftMap (map K L f) (map K L g) :=
  toPushout_comp_leftMap L f g

@[simp]
theorem pushoutComparison_comp_rightMap :
    (pushoutComparison L f g).toBoundedAlgHom.comp (map K L (AffinoidPushout.rightMap f g)) =
      AffinoidPushout.rightMap (map K L f) (map K L g) :=
  toPushout_comp_rightMap L f g

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension
