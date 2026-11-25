/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback


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

/-- The two source factors of the raw triangle map, kept as one morphism.
Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: sbc-lem-higher-image-raw-triangle-restriction). -/
def rawTriangleSource
    {C D E D' E' : Type*}
    [Category C] [Category D] [Category E] [Category D'] [Category E']
    (H : C ⥤ D) (H' : C ⥤ E) (P : D ⥤ E)
    (A : D ⥤ D') (B : E ⥤ E') (F : D' ⥤ E')
    (c : H' ⟶ H ⋙ P) (e : P ⋙ B ⟶ A ⋙ F) (U : C) :
    B.obj (H'.obj U) ⟶ F.obj (A.obj (H.obj U)) :=
  B.map (c.app U) ≫ e.app (H.obj U)





set_option backward.isDefEq.respectTransparency false in
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
  unfold rawTriangleMap
  change B.map (c.app T) ≫ e.app (H.obj T) ≫
    F.map (A.map (H.map b) ≫ z) ≫ s =
      B.map (H'.map b) ≫ B.map (c.app U) ≫ e.app (H.obj U) ≫ F.map z ≫ s
  have hc := congrArg B.map (c.naturality b)
  have hs := e.naturality (H.map b)
  simp only [Functor.comp_map, Functor.map_comp] at hc hs
  rw [F.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hs, ← reassoc_of% hc]



end AlgebraicGeometry.Etale
