/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageChartSystem

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Etale

lemma chartDiagram_obj_hom
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S)
    (i : I) (j : Over i) :
    ((cartesianChartDiagram f D i).obj j).hom =
      pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) := by
  rfl

lemma chartCone_pt_hom
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (i : I) :
    (cartesianChartCone f D c i).pt.hom =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) := by
  rfl


end AlgebraicGeometry.Etale
