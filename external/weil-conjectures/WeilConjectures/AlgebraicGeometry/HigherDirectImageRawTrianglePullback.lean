/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf

/-! # Raw pullback for a commutative triangle

Source: Stacks Project, Tags 03Q8 and 09Z1, canonical comparison maps.
(blueprint: sbc-lem-higher-image-raw-triangle-restriction).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The map on represented classes obtained from two comparison natural transformations
and a fixed coefficient morphism. This is the categorical formula for raw triangle pullback;
its factors are the comparisons used in Stacks Project, Tags 03Q8 and 09Z1. -/
def rawTriangleMap
    {C D E D' E' : Type*}
    [Category C] [Category D] [Category E] [Category D'] [Category E']
    [Preadditive D'] [Preadditive E']
    (H : C ⥤ D) (H' : C ⥤ E) (P : D ⥤ E)
    (A : D ⥤ D') (B : E ⥤ E') (F : D' ⥤ E')
    (c : H' ⟶ H ⋙ P) (e : P ⋙ B ⟶ A ⋙ F)
    (U : C) {K : D'} {K' : E'}
    (z : ((H ⋙ A).op ⋙ preadditiveYoneda.obj K).obj (op U))
    (s : F.obj K ⟶ K') :
    ((H' ⋙ B).op ⋙ preadditiveYoneda.obj K').obj (op U) :=
  B.map (c.app U) ≫ e.app (H.obj U) ≫ F.map z ≫ s

/-- Pullback of a derived class, followed by a specified coefficient morphism. The
coefficient morphism is given data, and no witness is chosen from an existence theorem. -/
noncomputable def higherDirectImageRawTrianglePullback
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K') (U : S.Etale)
    (z : (higherDirectImagePresheaf Λ h q K).obj (op U)) :
    (higherDirectImagePresheaf Λ h' q K').obj (op U) :=
  rawTriangleMap
    ((freeSheaf Λ S) ⋙ (h)^*[ModuleCat.{u + 1} Λ])
    ((freeSheaf Λ S) ⋙ (h')^*[ModuleCat.{u + 1} Λ])
    ((a)^*[ModuleCat.{u + 1} Λ])
    (DerivedCategory.Plus.singleFunctor _ 0)
    (DerivedCategory.Plus.singleFunctor _ 0)
    D+((a)^*[ModuleCat.{u + 1} Λ])
    (Functor.whiskerLeft (freeSheaf Λ S)
      (upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom)
    (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv
    U z ((D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
      (shiftFunctor _ q).map v)

private theorem trianglePullback_naturality
    {C D E D' E' : Type*}
    [Category C] [Category D] [Category E] [Category D'] [Category E']
    [Preadditive D'] [Preadditive E']
    (H : C ⥤ D) (H' : C ⥤ E) (P : D ⥤ E)
    (A : D ⥤ D') (B : E ⥤ E') (F : D' ⥤ E')
    (c : H' ⟶ H ⋙ P) (e : P ⋙ B ⟶ A ⋙ F)
    {U T : C} (b : T ⟶ U) {K : D'} {K' : E'}
    (z : ((H ⋙ A).op ⋙ preadditiveYoneda.obj K).obj (op U))
    (s : F.obj K ⟶ K') :
    rawTriangleMap H H' P A B F c e T
      (((H ⋙ A).op ⋙ preadditiveYoneda.obj K).map b.op z) s =
      ((H' ⋙ B).op ⋙ preadditiveYoneda.obj K').map b.op
        (rawTriangleMap H H' P A B F c e U z s) := by
  change B.map (c.app T) ≫ e.app (H.obj T) ≫
    F.map (A.map (H.map b) ≫ z) ≫ s =
      B.map (H'.map b) ≫ B.map (c.app U) ≫ e.app (H.obj U) ≫ F.map z ≫ s
  have hc := congrArg B.map (c.naturality b)
  have hs := e.naturality (H.map b)
  simp only [Functor.comp_map, Functor.map_comp] at hc hs
  rw [F.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hs, ← reassoc_of% hc]

set_option backward.isDefEq.respectTransparency true in
/-- Restriction naturality of the raw pullback.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-triangle-restriction).
Proof: Naturality of restriction through each displayed pullback factor, followed by
functoriality and associativity. -/
theorem higherDirectImageRawTrianglePullback_restriction
    (Λ : Type (u + 1)) [CommRing Λ] {Y Y' S : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (v : D+((a)^*[ModuleCat.{u + 1} Λ]).obj K ⟶ K')
    (U : S.Etale) (z : (higherDirectImagePresheaf Λ h q K).obj (op U))
    (T : S.Etale) (b : T ⟶ U) :
    higherDirectImageRawTrianglePullback Λ a h h' w q K K' v T
        ((higherDirectImagePresheaf Λ h q K).map b.op z) =
      (higherDirectImagePresheaf Λ h' q K').map b.op
        (higherDirectImageRawTrianglePullback Λ a h h' w q K K' v U z):= by
  unfold higherDirectImageRawTrianglePullback
  exact trianglePullback_naturality
    ((freeSheaf Λ S) ⋙ (h)^*[ModuleCat.{u + 1} Λ])
    ((freeSheaf Λ S) ⋙ (h')^*[ModuleCat.{u + 1} Λ])
    ((a)^*[ModuleCat.{u + 1} Λ])
    (DerivedCategory.Plus.singleFunctor _ 0)
    (DerivedCategory.Plus.singleFunctor _ 0)
    D+((a)^*[ModuleCat.{u + 1} Λ])
    (Functor.whiskerLeft (freeSheaf Λ S)
      (upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom)
    (((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).inv
    b z ((D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K ≫
      (shiftFunctor _ q).map v)

end AlgebraicGeometry.Etale
