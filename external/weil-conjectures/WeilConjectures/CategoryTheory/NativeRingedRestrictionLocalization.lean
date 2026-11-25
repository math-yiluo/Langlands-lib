/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
public import WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniverses
import WeilConjectures.CategoryTheory.NativeRingedRestrictionSheafification

/-! # Restriction of section localizations

Source: Stacks 03A0, 03CH, 03DA, 03DG, 04IY and 0996.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe c d vc vd r
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction

variable {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
  {K : GrothendieckTopology C} {J : GrothendieckTopology D}
  (F : C ⥤ D) [Functor.IsContinuous F K J]
  (R : Sheaf J CommRingCat.{max c d vc vd r})

/-- Restrict a compatible global section along the site functor.
Source: Stacks 03A0, 03CH, 03DA, 03DG.
(auxiliary; not a blueprint node). -/
def restrictedSection (s : (R.obj ⋙ forget CommRingCat).sections) :
    ((restrictedCommRing.{_, _, _, _, r} (K := K) F R).obj ⋙
      forget CommRingCat).sections :=
  ⟨fun X ↦ s.val (F.op.obj X), fun f ↦ s.property (F.op.map f)⟩

/-- Restriction commutes with localization at a compatible section.

Source: Stacks 03A0, 03CH, 03DA, 03DG, 04IY and 0996.
(auxiliary; not a blueprint node).

Proof: sectionwise restriction of the localization presheaf is the localization
presheaf of the restricted section: the rings, the sections and the universal
localization lifts are identical. Apply the sheafification restriction comparison. -/
theorem localizationRestriction [F.IsCocontinuous K J]
    [HasSheafify J CommRingCat.{max c d vc vd r}]
    [HasSheafify K CommRingCat.{max c d vc vd r}]
    [HasSheafify J AddCommGrpCat.{max c d vc vd r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
    [HasSheafify K AddCommGrpCat.{max c d vc vd r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
    (s : (R.obj ⋙ forget CommRingCat).sections) :
    Nonempty ((restrictModules.{_, _, _, _, r} (K := K) F R).obj
      (ringedSectionLocalizationOfUniverses R s) ≅
        ringedSectionLocalizationOfUniverses
          (restrictedCommRing.{_, _, _, _, r} (K := K) F R)
          (restrictedSection.{_, _, _, _, r} F R s)) := by
  let S := restrictedCommRing.{_, _, _, _, r} (K := K) F R
  let P := ringedSectionLocalizationPresheafOfUniverses R s
  obtain ⟨α⟩ := sheafificationRestriction.{_, _, _, _, r} (K := K) F R P
  let β : (PresheafOfModules.pushforward₀ F _).obj P ≅
      ringedSectionLocalizationPresheafOfUniverses S
        (restrictedSection.{_, _, _, _, r} F R s) :=
    PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intros; ext x; rfl)
  exact ⟨α ≪≫ (PresheafOfModules.sheafification (𝟙 _)).mapIso β⟩

end CategoryTheory.NativeRestriction
