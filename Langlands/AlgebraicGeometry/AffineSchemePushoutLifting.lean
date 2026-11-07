import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.LocalRing.Pullback

open CategoryTheory Limits Opposite
open AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.AffineSchemePushout

/-- A pushout square of the underlying presheafed spaces reflects to locally
ringed spaces. -/
theorem isPushout_locallyRingedSpace_of_presheafedSpace
    {W X Y Z : LocallyRingedSpace.{u}}
    {f : W ⟶ X} {g : W ⟶ Y} {i : X ⟶ Z} {j : Y ⟶ Z}
    (h : IsPushout (C := PresheafedSpace CommRingCat.{u})
      f.toHom g.toHom i.toHom j.toHom) :
    IsPushout f g i j := by
  have hs : IsPushout f.toShHom g.toShHom i.toShHom j.toShHom := by
    apply IsPushout.of_map_of_faithful SheafedSpace.forgetToPresheafedSpace
    exact h
  let := reflectsColimit_of_reflectsIsomorphisms (span f g)
    LocallyRingedSpace.forgetToSheafedSpace
  apply IsPushout.of_map_of_faithful LocallyRingedSpace.forgetToSheafedSpace
  exact hs

/-- The constructed colimit witness for the reflected locally ringed space cocone. -/
noncomputable def locallyRingedSpacePushoutIsColimit
    {W X Y Z : LocallyRingedSpace.{u}}
    {f : W ⟶ X} {g : W ⟶ Y} {i : X ⟶ Z} {j : Y ⟶ Z}
    (h : IsPushout (C := PresheafedSpace CommRingCat.{u})
      f.toHom g.toHom i.toHom j.toHom) :
    IsColimit (PushoutCocone.mk i j
      (isPushout_locallyRingedSpace_of_presheafedSpace h).w) :=
  (isPushout_locallyRingedSpace_of_presheafedSpace h).isColimit

/-- A pushout square of the underlying locally ringed spaces reflects to schemes. -/
theorem isPushout_scheme_of_locallyRingedSpace
    {W X Y Z : Scheme.{u}}
    {f : W ⟶ X} {g : W ⟶ Y} {i : X ⟶ Z} {j : Y ⟶ Z}
    (h : IsPushout f.toLRSHom g.toLRSHom i.toLRSHom j.toLRSHom) :
    IsPushout f g i j :=
  h.of_map_of_faithful Scheme.forgetToLocallyRingedSpace

variable {B C D : CommRingCat.{u}} {f : B ⟶ D} {g : C ⟶ D}

/-- The canonical spectrum square is a locally ringed space pushout whenever its
underlying presheafed space square is a pushout. -/
theorem isPushout_specLocallyRingedSpaceMap_of_presheafedSpace
    (h : IsPushout
      (Spec.toPresheafedSpace.map f.op) (Spec.toPresheafedSpace.map g.op)
      (Spec.toPresheafedSpace.map (CommRingCat.ofHom (f.hom.pullbackFst g.hom)).op)
      (Spec.toPresheafedSpace.map (CommRingCat.ofHom (f.hom.pullbackSnd g.hom)).op)) :
    IsPushout (Spec.locallyRingedSpaceMap f) (Spec.locallyRingedSpaceMap g)
      (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (f.hom.pullbackFst g.hom)))
      (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (f.hom.pullbackSnd g.hom))) :=
  isPushout_locallyRingedSpace_of_presheafedSpace h

/-- The canonical spectrum square is a scheme pushout whenever its underlying
presheafed space square is a pushout. -/
theorem isPushout_specMap_of_presheafedSpace
    (h : IsPushout
      (Spec.toPresheafedSpace.map f.op) (Spec.toPresheafedSpace.map g.op)
      (Spec.toPresheafedSpace.map (CommRingCat.ofHom (f.hom.pullbackFst g.hom)).op)
      (Spec.toPresheafedSpace.map (CommRingCat.ofHom (f.hom.pullbackSnd g.hom)).op)) :
    IsPushout (Spec.map f) (Spec.map g)
      (Spec.map (CommRingCat.ofHom (f.hom.pullbackFst g.hom)))
      (Spec.map (CommRingCat.ofHom (f.hom.pullbackSnd g.hom))) :=
  isPushout_scheme_of_locallyRingedSpace
    (isPushout_specLocallyRingedSpaceMap_of_presheafedSpace h)

end Langlands.AlgebraicGeometry.AffineSchemePushout
