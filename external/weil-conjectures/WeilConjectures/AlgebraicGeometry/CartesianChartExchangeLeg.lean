/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback

-- Internal comparison lemmas are shared through private imports.
set_option linter.privateModule false

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

private noncomputable def cartesianChartPullbackLeg
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (i : I) (j : Over i) :
    pullback (c.π.app i).left (pullback.snd f (D.obj i).hom) ⟶
      pullback (D.map j.hom).left (pullback.snd f (D.obj i).hom) :=
  pullback.lift
    (pullback.fst (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
      (c.π.app j.left).left)
    (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
    (by
      rw [Category.assoc]
      rw [← pullback.condition]
      congr 1
      exact congrArg (fun t ↦ t.left) (c.w j.hom))

-- Expanding chart comparisons and adjunction units needs a local reduction budget.
private lemma cartesianChartCone_leg_eq_pullback
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (i : I) (j : Over i) :
    ((cartesianChartCone f D c i).π.app j).left =
      cartesianChartPullbackLeg f D c i j := by
  change pullback.lift _ _ _ = cartesianChartPullbackLeg f D c i j
  change cartesianChartPullbackLeg f D c i j = cartesianChartPullbackLeg f D c i j
  rfl

end AlgebraicGeometry.Etale
