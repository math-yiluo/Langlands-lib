/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalization
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs

/-! # Detecting the comparison of localization cocones on their unit legs -/

@[expose] public section

universe u v w x y
open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A morphism between localization telescopes is determined by its zeroth leg if
multiplication by ℓ is invertible at its target. In particular, if a functor sends both
cocones to colimits, it sends that morphism to an isomorphism.
Source: Bhatt--Scholze, Lemma 6.8.2, universal property of localization.
(auxiliary; not a blueprint node).
Proof. Cocone compatibility identifies the nth leg with ℓ times the next leg.
Induct on n and cancel multiplication by ℓ at the target to check all legs from the
zeroth leg. This gives a morphism between the two colimit cocones; uniqueness of
colimits makes its vertex map invertible. -/
theorem integralLocalization_cocone_map_isIso (ℓ : ℕ)
    {C : Type u} [Category.{v} C] [Preadditive C]
    {K : C} (c d : Cocone (Mod.smulSequence K ℓ))
    [IsIso (ℓ • 𝟙 d.pt)] (g : c.pt ⟶ d.pt)
    (hzero : c.ι.app 0 ≫ g = d.ι.app 0)
    {B : Type w} [Category.{x} B] (F : C ⥤ B)
    (hc : IsColimit (F.mapCocone (c.whisker
      (ULift.orderIso : ULift.{y} ℕ ≃o ℕ).equivalence.functor)))
    (hd : IsColimit (F.mapCocone (d.whisker
      (ULift.orderIso : ULift.{y} ℕ ≃o ℕ).equivalence.functor))) :
    IsIso (F.map g) := by
  have hleg := integralLocalization_coconeLegs ℓ c d g hzero
  let h : F.mapCocone (c.whisker
      (ULift.orderIso : ULift.{y} ℕ ≃o ℕ).equivalence.functor) ⟶
      F.mapCocone (d.whisker
      (ULift.orderIso : ULift.{y} ℕ ≃o ℕ).equivalence.functor) :=
    ⟨F.map g, fun n ↦ by
      change F.map (c.ι.app n.down) ≫ F.map g = F.map (d.ι.app n.down)
      rw [← F.map_comp, hleg]⟩
  have : IsIso h := IsColimit.hom_isIso hc hd h
  exact (Cocone.forget _ ⋙ 𝟭 B).map_isIso h

end AlgebraicGeometry.ProEtale.CondensedRing
