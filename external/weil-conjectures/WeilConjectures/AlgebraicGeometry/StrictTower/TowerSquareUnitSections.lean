/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
/-! # Unit sections of the canonical compositor square
Source: Stacks, Tags 04J0 and 07A7
(blueprint: lem-cbc-tower-square-unit-sections).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
attribute [-instance] CategoryTheory.catToReflQuiver
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]
/-- The canonical module adjunction unit evaluated on a section.
Source: Stacks, Tag 04J0 (blueprint: lem-cbc-tower-square-unit-sections). -/
def towerUnitSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules B Y) (V : Y.ProEt) (s : M.val.obj (op V)) :
    ((modulePullback B f).obj M).val.obj (op ((Scheme.proEtaleBaseChange f).obj V)) :=
  (((Scheme.proEtaleRingModuleAdjunction f (coefficients B Y) (coefficients B X)
    (constantRingIso B f)).unit.app M).val.app (op V)) s

attribute [local irreducible] moduleSquareG modulePullback moduleGComp moduleRComp
  Scheme.proEtaleRingModuleAdjunction constantRingIso towerUnitSection


end AlgebraicGeometry.ProEtale.StrictTower

attribute [instance] CategoryTheory.catToReflQuiver
