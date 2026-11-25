/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
import all WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniverses

/-! # Sheafification under restriction of sites

Source: Stacks 03A0, 03CH, 03DA, 03DG and 0996.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe c d vc vd r
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction

/-- Continuous and cocontinuous restriction commutes with module sheafification.

Source: Stacks 03A0, 03CH, 03DA, 03DG and 0996.
(auxiliary; not a blueprint node).

Proof: the sheafification unit is locally bijective. Cocontinuity preserves this
property after restriction, and continuity makes its target a sheaf. The universal
property of module sheafification therefore identifies the restricted target with
the sheafification of the restricted presheaf. -/
theorem sheafificationRestriction
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    {K : GrothendieckTopology C} {J : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F K J] [F.IsCocontinuous K J]
    (R : Sheaf J CommRingCat.{max c d vc vd r})
    [HasSheafify J AddCommGrpCat.{max c d vc vd r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
    [HasSheafify K AddCommGrpCat.{max c d vc vd r}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
    (P : PresheafOfModules.{max c d vc vd r}
      (NativeRings.{max c d vc vd r, d, vd} R).obj) :
    let T := restrictModules.{_, _, _, _, r} (K := K) F R
    let R' := NativeRings.{max c d vc vd r, c, vc}
      (restrictedCommRing.{_, _, _, _, r} (K := K) F R)
    Nonempty (T.obj ((PresheafOfModules.sheafification (𝟙 _)).obj P) ≅
      (PresheafOfModules.sheafification (𝟙 R'.obj)).obj
        ((PresheafOfModules.pushforward₀ F _).obj P)) := by
  let T := restrictModules.{_, _, _, _, r} (K := K) F R
  let R' := NativeRings.{max c d vc vd r, c, vc}
    (restrictedCommRing.{_, _, _, _, r} (K := K) F R)
  let A := (PresheafOfModules.sheafification (𝟙 _)).obj P
  let η : P ⟶ A.val := (PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app P
  let P' := (PresheafOfModules.pushforward₀ F _).obj P
  let φ : P' ⟶ (T.obj A).val := (PresheafOfModules.pushforward₀ F _).map η
  have hi : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map η) := by
    change Presheaf.IsLocallyInjective J (toSheafify J P.presheaf)
    infer_instance
  have hs : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map η) := by
    change Presheaf.IsLocallySurjective J (toSheafify J P.presheaf)
    infer_instance
  have := hi
  have := hs
  have hiφ : PresheafOfModules.IsLocallyInjective K φ :=
    Presheaf.isLocallyInjective_whisker K J F
      ((PresheafOfModules.toPresheaf _).map η)
  have hsφ : PresheafOfModules.IsLocallySurjective K φ :=
    Presheaf.isLocallySurjective_whisker K J F
      ((PresheafOfModules.toPresheaf _).map η)
  obtain ⟨e, _⟩ := @RingedLocalizationComparison.comparison.{max c d vc vd r, c, vc}
    C _ K _ _ R' P' (T.obj A) φ hiφ hsφ
  exact ⟨e⟩

end CategoryTheory.NativeRestriction
