/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyClass
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeEvaluation
import WeilConjectures.AlgebraicGeometry.CartesianChartExchangeChartMap

/-! # Evaluation of the restricted chart cone map

Source: Stacks Project, Tags 0EYM and 03Q8.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local irreducible] cohomology upperStar rawAffineComplexPullback
  rightDerivedGlobalSections DerivedCategory.Q

/-- The specified raw pullback of the canonical inverse-evaluation stage class.
Source: Stacks Project, Tags 0EYM and 03Q8.
(blueprint: def-sc-cartesian-chart-restricted-raw-class). -/
@[irreducible]
noncomputable def cartesianChartRestrictedRawClass
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale)
    (j : Over i)
    (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D i).obj j) V)
    (hl₂ : ((cartesianChartCone f D c i).π.app j).left ≫
      pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom)) :
    (abelianHigherDirectImageRawPresheaf
      (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) q
      (((pullback.snd (c.π.app i).left
        (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V) :=
  let h := pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
    pullback.snd f (D.obj i).hom
  let h' := pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
    pullback.snd f (D.obj i).hom
  let l : pullback (c.π.app i).left (pullback.snd f (D.obj i).hom) ⟶
      pullback (D.map j.hom).left (pullback.snd f (D.obj i).hom) :=
    ((cartesianChartCone f D c i).π.app j).left
  let wl : l ≫ h = h' :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t ↦ t ≫ pullback.snd f (D.obj i).hom) hl₂)
  let G := ((pullback.snd (D.map j.hom).left
      (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let G' := ((pullback.snd (c.π.app i).left
      (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let φ := (upperStarComp AddCommGrpCat.{u + 1} l
    (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))
    (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
    hl₂.symm).inv.app (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let z := rawRestrictedCohomologyClass h q G V x
  let z' := abelianHigherDirectImageRawPullback l h h' wl q G G' φ V z
  z'

/-- The defining equation of the cached chart raw class.
Source: Stacks Project, Tags 0EYM and 03Q8.
(blueprint: def-sc-cartesian-chart-restricted-raw-class).

Proof: Unfold the real raw-pullback construction; both sides are identical. -/
theorem cartesianChartRestrictedRawClass_eq
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale)
    (j : Over i)
    (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D i).obj j) V)
    (hl₂ : ((cartesianChartCone f D c i).π.app j).left ≫
      pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom)) :
    cartesianChartRestrictedRawClass f D c F q i V j x hl₂ =
  let h := pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
    pullback.snd f (D.obj i).hom
  let h' := pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
    pullback.snd f (D.obj i).hom
  let l : pullback (c.π.app i).left (pullback.snd f (D.obj i).hom) ⟶
      pullback (D.map j.hom).left (pullback.snd f (D.obj i).hom) :=
    ((cartesianChartCone f D c i).π.app j).left
  let wl : l ≫ h = h' :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t ↦ t ≫ pullback.snd f (D.obj i).hom) hl₂)
  let G := ((pullback.snd (D.map j.hom).left
      (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let G' := ((pullback.snd (c.π.app i).left
      (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let φ := (upperStarComp AddCommGrpCat.{u + 1} l
    (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))
    (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
    hl₂.symm).inv.app (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let z := rawRestrictedCohomologyClass h q G V x
  let z' := abelianHigherDirectImageRawPullback l h h' wl q G G' φ V z
  z' := by
  exact cartesianChartRestrictedRawClass.eq_def f D c F q i V j x hl₂

attribute [local irreducible] cartesianChartCohomologyIso cartesianChartRawAdjunctionIso
  rawRestrictedCohomologyComparison abelianHigherDirectImageRawPullback
  rawAffineRestrictedCohomologyMap

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency true in
/-- Evaluation at the apex sends the restricted cohomology cone map to the
raw pullback of the canonical inverse-evaluation class.
Source: Stacks Project, Tags 0EYM and 03Q8.
(blueprint: lem-sc-cartesian-chart-restricted-map-evaluation).

Proof: First identify restrictedOverCohomologyMap with the raw affine map for
l, h and h'. Unfold their literal derived pullback and coefficient formulas. The
coefficient morphisms agree by the displayed second-projection equality and
proof irrelevance. Apply rawRestrictedCohomologyClass_map: the raw affine map
of x is evaluation of z'. Finally apply the proved chartCohomologyIso_eval
from CartesianChartExchangeEvaluation to z'. Its free-source precomposition
is exactly the map displayed here. Combine these two equalities by congruence
and transitivity. This calculation uses neither exchange nor the stage lift,
and holds for degree zero and empty test objects without changes. -/
theorem cartesianChartRestrictedCohomologyMap_eval
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (U : c.pt.left.Etale)
    (r : U.left ⟶ V.left) (hr : IsPullback r U.hom V.hom (c.π.app i).left)
    (j : Over i)
    (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D i).obj j) V)
    (hl₂ : ((cartesianChartCone f D c i).π.app j).left ≫
      pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom)) :
  (cartesianChartCohomologyIso f (D.obj i).hom (c.π.app i).left c.pt.hom
    (Over.w (c.π.app i)).symm F q V U r hr).hom
    (restrictedOverCohomologyMap (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartCone f D c i).π.app j) V x) =
  (DerivedCategory.Plus.singleFunctor _ 0).map
    (abelianFreeRepresentablePullbackSquareIso (c.π.app i).left V U r hr).hom ≫
    (cartesianChartRawAdjunctionIso f (D.obj i).hom (c.π.app i).left c.pt.hom
      (Over.w (c.π.app i)).symm F q V).hom
      (cartesianChartRestrictedRawClass f D c F q i V j x hl₂) := by
  let h := pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
    pullback.snd f (D.obj i).hom
  let h' := pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
    pullback.snd f (D.obj i).hom
  let l : pullback (c.π.app i).left (pullback.snd f (D.obj i).hom) ⟶
      pullback (D.map j.hom).left (pullback.snd f (D.obj i).hom) :=
    ((cartesianChartCone f D c i).π.app j).left
  have wl : l ≫ h = h' :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t ↦ t ≫ pullback.snd f (D.obj i).hom) hl₂)
  let G := ((pullback.snd (D.map j.hom).left
      (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let G' := ((pullback.snd (c.π.app i).left
      (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let φ := (upperStarComp AddCommGrpCat.{u + 1} l
    (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))
    (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
    hl₂.symm).inv.app (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  have hm := congrArg (fun t ↦ t x) (chartRestrictedMap_eq_rawAffine f D c F q i V j hl₂ wl)
  have hn := rawRestrictedCohomologyClass_map l h h' wl q G G' φ V x
  have he := chartCohomologyIso_eval f (D.obj i).hom (c.π.app i).left c.pt.hom
    (Over.w (c.π.app i)).symm F q V U r hr
    (cartesianChartRestrictedRawClass f D c F q i V j x hl₂)
  have hz := cartesianChartRestrictedRawClass_eq f D c F q i V j x hl₂
  dsimp only [] at hz
  have hn' := (hm.trans hn).trans
    (congrArg (fun y ↦ rawRestrictedCohomologyComparison h' q G' V y) hz.symm)
  have hc := congrArg
    (fun y ↦ (cartesianChartCohomologyIso f (D.obj i).hom (c.π.app i).left c.pt.hom
      (Over.w (c.π.app i)).symm F q V U r hr).hom y) hn'
  exact hc.trans he

end AlgebraicGeometry.Etale
