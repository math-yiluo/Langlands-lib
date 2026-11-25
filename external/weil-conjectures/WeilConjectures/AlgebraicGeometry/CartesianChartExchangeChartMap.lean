/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianChartExchangeMapBridge
public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageChartSystem
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeObjects

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

lemma chartRestrictedMap_eq_rawAffine
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (j : Over i)
    (hl₂ : ((cartesianChartCone f D c i).π.app j).left ≫
      pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
    (hw : ((cartesianChartCone f D c i).π.app j).left ≫
      (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) :
    restrictedOverCohomologyMap (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartCone f D c i).π.app j) V =
    rawAffineRestrictedCohomologyMap ((cartesianChartCone f D c i).π.app j).left
      (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom)
      (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) hw q
      (((pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u
        + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
      (((pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
      ((upperStarComp AddCommGrpCat.{u + 1} ((cartesianChartCone f D c i).π.app j).left
        (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))
        (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
        hl₂.symm).inv.app
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) V := by
  rfl

lemma chartRestrictedMap_apply_eq_rawAffine
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (j : Over i)
    (hl₂ : ((cartesianChartCone f D c i).π.app j).left ≫
      pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
    (hw : ((cartesianChartCone f D c i).π.app j).left ≫
      (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom)
    (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D i).obj j) V) :
    restrictedOverCohomologyMap (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartCone f D c i).π.app j) V x =
    rawAffineRestrictedCohomologyMap ((cartesianChartCone f D c i).π.app j).left
      (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom)
      (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) hw q
      (((pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u
        + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
      (((pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
      ((upperStarComp AddCommGrpCat.{u + 1} ((cartesianChartCone f D c i).π.app j).left
        (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))
        (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
        hl₂.symm).inv.app
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) V x := by
  exact congrArg (fun t ↦ t x)
    (chartRestrictedMap_eq_rawAffine f D c F q i V j hl₂ hw)


end AlgebraicGeometry.Etale
