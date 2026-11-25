/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.CompactificationChosenComposition
public import Mathlib.CategoryTheory.Whiskering

/-! # Transport of compactification words through fixed realizations

## References

* Stacks 0F7J--0F7K, conjugation by the fixed realization equivalences
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProperOpenCalculus
attribute [local implicit_reducible] H Compactification.copy

variable {A : Scheme.{u} → Prop} (F : ProperOpenCalculus.{u, v, w} A)

set_option linter.checkUnivs false in
/-- Fixed native functors and their comparison to the literal proper/open word.
The comparison is part of the coordinates, not a map recovered by evaluation. -/
structure CompactificationRealization where
  obj : {X : Scheme.{u} // A X} → Type w'
  [category (X : {X : Scheme.{u} // A X}) : Category.{v'} (obj X)]
  coordinate (X : {X : Scheme.{u} // A X}) : obj X ≌ F.obj X
  H (X Y : {X : Scheme.{u} // A X}) {f : X.val ⟶ Y.val} [QuasiCompact f]
    (c : Compactification f) (hc : A c.Z) : obj X ⥤ obj Y
  comparison (X Y : {X : Scheme.{u} // A X}) {f : X.val ⟶ Y.val} [QuasiCompact f]
    (c : Compactification f) (hc : A c.Z) :
    H X Y c hc ⋙ (coordinate Y).functor ≅ (coordinate X).functor ⋙ F.H X Y c hc

namespace CompactificationRealization
attribute [instance] category
variable {F} (R : CompactificationRealization.{u, v, w, v', w'} F) (G : Geometry A)

/-- Transport a known model comparison through a fully faithful target coordinate. -/
def refinement (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f) (hc : A c.Z) (hd : A d.Z) :
    R.H X Y c hc ≅ R.H X Y d hd :=
  ((R.coordinate Y).fullyFaithfulFunctor.whiskeringRight _).preimageIso
    (R.comparison X Y c hc ≪≫
      Functor.isoWhiskerLeft (R.coordinate X).functor (F.comparison G X Y f c d hc hd) ≪≫
        (R.comparison X Y d hd).symm)

/-- Transport the actual binary word through the fixed coordinates. -/
def composition (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val) (fg : X.val ⟶ Z.val) (wfg : f ≫ g = fg)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [QuasiCompact fg]
    (c : Compactification f) (d : Compactification g) (e : Compactification fg)
    (hc : A c.Z) (hd : A d.Z) (he : A e.Z) :
    R.H X Y c hc ⋙ R.H Y Z d hd ≅ R.H X Z e he :=
  ((R.coordinate Z).fullyFaithfulFunctor.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (R.H X Y c hc) (R.comparison Y Z d hd) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (R.comparison X Y c hc) (F.H Y Z d hd) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (R.coordinate X).functor
        (F.namedBinary G X Y Z f g fg wfg c d e hc hd he) ≪≫
      (R.comparison X Z e he).symm)

/-- The identity word transported through the fixed coordinates. -/
def identity (X : {X : Scheme.{u} // A X})
    (c : Compactification (𝟙 X.val)) (hc : A c.Z) :
    R.H X X c hc ≅ 𝟭 (R.obj X) :=
  ((R.coordinate X).fullyFaithfulFunctor.whiskeringRight _).preimageIso
    (R.comparison X X c hc ≪≫
      Functor.isoWhiskerLeft (R.coordinate X).functor (F.chosenIdentity G X c hc) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- The composition map is the actual conjugated binary word at every native object. -/
theorem composition_map (X Y Z : {X : Scheme.{u} // A X})
    (f : X.val ⟶ Y.val) (g : Y.val ⟶ Z.val) (fg : X.val ⟶ Z.val) (wfg : f ≫ g = fg)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] [QuasiCompact fg]
    (c : Compactification f) (d : Compactification g) (e : Compactification fg)
    (hc : A c.Z) (hd : A d.Z) (he : A e.Z) (M : R.obj X) :
    (R.coordinate Z).functor.map
      ((R.composition G X Y Z f g fg wfg c d e hc hd he).hom.app M) =
      (R.comparison Y Z d hd).hom.app ((R.H X Y c hc).obj M) ≫
        (F.H Y Z d hd).map ((R.comparison X Y c hc).hom.app M) ≫
        (F.namedBinary G X Y Z f g fg wfg c d e hc hd he).hom.app
          ((R.coordinate X).functor.obj M) ≫ (R.comparison X Z e he).inv.app M := by
  have h := ((R.coordinate Z).fullyFaithfulFunctor.whiskeringRight _).map_preimage
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (R.H X Y c hc) (R.comparison Y Z d hd) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (R.comparison X Y c hc) (F.H Y Z d hd) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (R.coordinate X).functor
        (F.namedBinary G X Y Z f g fg wfg c d e hc hd he) ≪≫
      (R.comparison X Z e he).symm).hom
  simpa only [composition, identity, Functor.FullyFaithful.preimageIso_hom,
    Functor.whiskeringRight, Functor.comp_obj, Functor.id_obj,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Category.id_comp, Category.comp_id, Category.assoc] using NatTrans.congr_app h M

/-- Identity transport at a native object. -/
theorem identity_map (X : {X : Scheme.{u} // A X})
    (c : Compactification (𝟙 X.val)) (hc : A c.Z) (M : R.obj X) :
    (R.coordinate X).functor.map ((R.identity G X c hc).hom.app M) =
      (R.comparison X X c hc).hom.app M ≫
        (F.chosenIdentity G X c hc).hom.app ((R.coordinate X).functor.obj M) := by
  have h := ((R.coordinate X).fullyFaithfulFunctor.whiskeringRight _).map_preimage
    (R.comparison X X c hc ≪≫
      Functor.isoWhiskerLeft (R.coordinate X).functor (F.chosenIdentity G X c hc) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm).hom
  simpa only [composition, identity, Functor.FullyFaithful.preimageIso_hom,
    Functor.whiskeringRight, Functor.comp_obj, Functor.id_obj,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Category.id_comp, Category.comp_id, Category.assoc] using NatTrans.congr_app h M

/-- Naturality pins the image of every native support morphism. -/
theorem support_map (X Y : {X : Scheme.{u} // A X}) {f : X.val ⟶ Y.val}
    [QuasiCompact f] (c : Compactification f) (hc : A c.Z)
    {M N : R.obj X} (t : M ⟶ N) :
    (R.coordinate Y).functor.map ((R.H X Y c hc).map t) =
      (R.comparison X Y c hc).hom.app M ≫
        (F.H X Y c hc).map ((R.coordinate X).functor.map t) ≫
          (R.comparison X Y c hc).inv.app N := by
  have h := (R.comparison X Y c hc).hom.naturality t
  dsimp only [Functor.comp_map] at h
  rw [← Category.assoc, ← h]
  simp

/-- Left identity for native composition. -/
theorem composition_left (X Y : {X : Scheme.{u} // A X}) (f : X.val ⟶ Y.val)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (hc : A c.Z)
    (i : Compactification (𝟙 X.val)) (hi : A i.Z) (M : R.obj X) :
    (R.composition G X X Y (𝟙 X.val) f f (Category.id_comp f) i c c hi hc hc).hom.app M =
      (R.H X Y c hc).map ((R.identity G X i hi).hom.app M) := by
  apply (R.coordinate Y).functor.map_injective
  simp only [composition_map, support_map, identity_map, Functor.map_comp]
  rw [F.namedBinary_left G X Y f c hc i hi]
  simp

end CompactificationRealization
end AlgebraicGeometry.ProperOpenCalculus
