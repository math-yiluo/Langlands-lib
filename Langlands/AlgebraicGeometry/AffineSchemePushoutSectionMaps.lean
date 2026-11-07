import Langlands.AlgebraicGeometry.AffineSchemePushoutSheaf

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry TopCat.Presheaf

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.AffineSchemePushout

variable {B C D : CommRingCat.{u}} (f : B ⟶ D) (g : C ⟶ D)

/-- The first pushed spectrum section map is the first sheaf pullback map. -/
theorem specPushforwardFst_eq :
    (pushforward CommRingCat
      (Spec.topMap (CommRingCat.ofHom (f.hom.pullbackFst g.hom)))).map
        (Spec.sheafedSpaceMap f).hom.c =
      (overSheafFst f.hom g.hom).hom := by
  rfl

/-- Transporting the second pushed spectrum section map gives the second
map in the structure-sheaf pullback square. -/
theorem specPushforwardSnd_eq
    (h : Spec.topMap g ≫
        Spec.topMap (CommRingCat.ofHom (f.hom.pullbackSnd g.hom)) =
      Spec.topMap f ≫
        Spec.topMap (CommRingCat.ofHom (f.hom.pullbackFst g.hom))) :
    (pushforward CommRingCat
      (Spec.topMap (CommRingCat.ofHom (f.hom.pullbackSnd g.hom)))).map
        (Spec.sheafedSpaceMap g).hom.c ≫
      (pushforwardEq h (Spec.structureSheaf D).obj).hom =
        (overSheafSnd f.hom g.hom).hom := by
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  simp only [TopCat.Presheaf.comp_app, pushforward_map_app', pushforwardEq_hom_app]
  simp only [CommRingCat.hom_comp]
  rw [← eqToHom_op]
  erw [← StructureSheaf.comap_id_eq_map]
  erw [← StructureSheaf.comap_comp]
  simp only [RingHom.id_comp]
  rfl
  all_goals rw [h]

/-- The canonical presheaf square with actual spectrum section maps is a pullback. -/
theorem isPullback_specPresheaf
    (h : Spec.topMap g ≫
        Spec.topMap (CommRingCat.ofHom (f.hom.pullbackSnd g.hom)) =
      Spec.topMap f ≫
        Spec.topMap (CommRingCat.ofHom (f.hom.pullbackFst g.hom))) :
    IsPullback
      (Spec.sheafedSpaceMap (CommRingCat.ofHom (f.hom.pullbackFst g.hom))).hom.c
      (Spec.sheafedSpaceMap (CommRingCat.ofHom (f.hom.pullbackSnd g.hom))).hom.c
      ((pushforward CommRingCat
        (Spec.topMap (CommRingCat.ofHom (f.hom.pullbackFst g.hom)))).map
          (Spec.sheafedSpaceMap f).hom.c)
      ((pushforward CommRingCat
        (Spec.topMap (CommRingCat.ofHom (f.hom.pullbackSnd g.hom)))).map
          (Spec.sheafedSpaceMap g).hom.c ≫
        (pushforwardEq h (Spec.structureSheaf D).obj).hom) := by
  rw [specPushforwardFst_eq, specPushforwardSnd_eq]
  exact isPullback_overPresheaf f.hom g.hom

/-- A limit witness for the canonical square of actual spectrum section maps. -/
def specPresheafPullbackIsLimit
    (h : Spec.topMap g ≫
        Spec.topMap (CommRingCat.ofHom (f.hom.pullbackSnd g.hom)) =
      Spec.topMap f ≫
        Spec.topMap (CommRingCat.ofHom (f.hom.pullbackFst g.hom))) :
    IsLimit (PullbackCone.mk
      (Spec.sheafedSpaceMap (CommRingCat.ofHom (f.hom.pullbackFst g.hom))).hom.c
      (Spec.sheafedSpaceMap (CommRingCat.ofHom (f.hom.pullbackSnd g.hom))).hom.c
      (isPullback_specPresheaf f g h).w) :=
  (isPullback_specPresheaf f g h).isLimit

end Langlands.AlgebraicGeometry.AffineSchemePushout
