/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import WeilConjectures.CategoryTheory.RingedSiteModules

set_option linter.privateModule false

/-!
# Tensor products and restriction to a localized ringed site

Source: Stacks Project, Modules on Sites, Tags 03EL and 03DH
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe uC vC r m

open CategoryTheory Opposite Functor

namespace SheafOfModules

section SheafificationComparison

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify J AddCommGrpCat.{m}]
  (R : Sheaf J RingCat.{r}) (U : C)
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{m}]

private noncomputable def overSheafificationMap (P : PresheafOfModules.{m} R.obj) :
    (PresheafOfModules.sheafification (R := R.over U) (𝟙 _)).obj
      ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).obj P) ⟶
        ((PresheafOfModules.sheafification (R := R) (𝟙 _)).obj P).over U :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).symm
    ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.app P))

set_option backward.isDefEq.respectTransparency false in
private lemma overSheafificationMap_unit (P : PresheafOfModules.{m} R.obj) :
    toSheafify (J.over U) ((Over.forget U).op ⋙ P.presheaf) ≫
        (PresheafOfModules.toPresheaf _).map (overSheafificationMap R U P).val =
      whiskerLeft (Over.forget U).op (toSheafify J P.presheaf) := by
  have h := (PresheafOfModules.sheafificationHomEquiv (R := R.over U) (𝟙 _)
    (P := (PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).obj P)
    (F := ((PresheafOfModules.sheafification (R := R) (𝟙 _)).obj P).over U)).apply_symm_apply
    ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.app P))
  exact congrArg ((PresheafOfModules.toPresheaf (R.over U).obj).map) h

private lemma overSheafificationMap_isIso (P : PresheafOfModules.{m} R.obj) :
    IsIso (overSheafificationMap R U P) := by
  let a := toSheafify (J.over U) ((Over.forget U).op ⋙ P.presheaf)
  let b := (PresheafOfModules.toPresheaf _).map (overSheafificationMap R U P).val
  have hi : Presheaf.IsLocallyInjective (J.over U)
      (whiskerLeft (Over.forget U).op (toSheafify J P.presheaf)) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) _
  have hs : Presheaf.IsLocallySurjective (J.over U)
      (whiskerLeft (Over.forget U).op (toSheafify J P.presheaf)) :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _
  have hi' : Presheaf.IsLocallyInjective (J.over U) b := by
    rw [← Presheaf.comp_isLocallyInjective_iff (J.over U) a b]
    rw [overSheafificationMap_unit]
    exact hi
  have hs' : Presheaf.IsLocallySurjective (J.over U) b := by
    rw [← Presheaf.comp_isLocallySurjective_iff (J.over U) a b]
    rw [overSheafificationMap_unit]
    exact hs
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (R.over U))]
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · exact (Sheaf.isLocallyInjective_sheafToPresheaf_map_iff _).mp hi'
  · exact (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).mp hs'

set_option backward.isDefEq.respectTransparency false in
private lemma overSheafificationMap_naturality {P Q : PresheafOfModules.{m} R.obj}
    (f : P ⟶ Q) :
    (PresheafOfModules.sheafification (R := R.over U) (𝟙 _)).map
        ((PresheafOfModules.pushforward (F := Over.forget U) (𝟙 _)).map f) ≫
        overSheafificationMap R U Q =
      overSheafificationMap R U P ≫
        ((PresheafOfModules.sheafification (R := R) (𝟙 _)).map f).over U := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf _).map_injective
  apply sheafify_hom_ext (J.over U) _ _
    (((PresheafOfModules.sheafification (R := R) (𝟙 _)).obj Q).over U).isSheaf
  change toSheafify (J.over U) ((Over.forget U).op ⋙ P.presheaf) ≫
      (sheafifyMap (J.over U)
        (whiskerLeft (Over.forget U).op ((PresheafOfModules.toPresheaf _).map f)) ≫
        (PresheafOfModules.toPresheaf _).map (overSheafificationMap R U Q).val) =
    toSheafify (J.over U) ((Over.forget U).op ⋙ P.presheaf) ≫
      ((PresheafOfModules.toPresheaf _).map (overSheafificationMap R U P).val ≫
        whiskerLeft (Over.forget U).op
          (sheafifyMap J ((PresheafOfModules.toPresheaf _).map f)))
  rw [← toSheafify_naturality_assoc]
  erw [overSheafificationMap_unit R U Q]
  rw [← Category.assoc, overSheafificationMap_unit R U P]
  exact (whiskerLeft_comp _ _ _).symm.trans
    ((congrArg (whiskerLeft (Over.forget U).op) (toSheafify_naturality J _)).trans
      (whiskerLeft_comp _ _ _))

end SheafificationComparison

end SheafOfModules
