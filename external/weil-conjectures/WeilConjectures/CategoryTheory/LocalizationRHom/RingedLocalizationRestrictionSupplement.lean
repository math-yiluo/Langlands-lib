/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedLocalizationModelsSupplement
public import WeilConjectures.Algebra.Homology.SliceModuleSheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.AlgebraicGeometry.RingedLocalizationRestriction

/-! # Restriction of fraction sheaves and localized complexes

Source: Stacks Project, Tags 04IX, 08JB and 0996.
(blueprint: lem-weil-pbc-ringed-localization-restriction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.LocalizationRHom

section General

variable {D E : Type u} [SmallCategory D] [SmallCategory E]
  {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  (F : D ⥤ E) [Functor.IsContinuous F K L]
  (T : Sheaf L CommRingCat.{u})

end General

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})

/-- Sheafification commutes with the further slice restriction used here.
Source: Stacks 03CY, 03DH and 04IX
(blueprint: lem-weil-pbc-ringed-localization-restriction). -/
def sheafificationOverMapIso {U V : C} (a : V ⟶ U) :
    PresheafOfModules.sheafification
      (𝟙 ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (R.over U)).obj) ⋙
      SheafOfModules.overMap.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) a ≅
    PresheafOfModules.pushforward₀ (Over.map a)
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U)).obj ⋙
      PresheafOfModules.sheafification
        (R₀ := ((sheafCompose (J.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (R.over V)).obj)
        (R := (sheafCompose (J.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over V))
        (𝟙 ((sheafCompose (J.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (R.over V)).obj) :=
  SheafOfModules.sliceSheafificationIso (J := J.over V) (K := J.over U) (Over.map a)
    ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))

/-- A fraction presheaf restricted further in a slice has the restricted denominator.
Source: Stacks 04IX and 0996
(blueprint: lem-weil-pbc-ringed-localization-restriction). -/
def coefficientPresheafIso {U V : C} (a : V ⟶ U) (f : R.obj.obj (op U)) :
    (PresheafOfModules.pushforward₀ (Over.map a)
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U)).obj).obj
      (ringedSectionLocalizationPresheaf (R.over U) (ringedSliceSection R U f)) ≅
    ringedSectionLocalizationPresheaf (R.over V)
      (ringedSliceSection R V (R.obj.map a.op f)) := by
  have h : restrictedSection (K := J.over V) (L := J.over U) (Over.map a) (R.over U)
      (ringedSliceSection R U f) = ringedSliceSection R V (R.obj.map a.op f) := by
    apply Subtype.ext
    funext W
    change R.obj.map (W.unop.hom ≫ a).op f =
      R.obj.map W.unop.hom.op (R.obj.map a.op f)
    rw [op_comp, R.obj.map_comp]
    rfl
  exact restrictionPresheafIso (K := J.over V) (L := J.over U) (Over.map a) (R.over U)
    (ringedSliceSection R U f) ≪≫
      eqToIso (congrArg (ringedSectionLocalizationPresheaf (R.over V)) h)

end CategoryTheory.LocalizationRHom
