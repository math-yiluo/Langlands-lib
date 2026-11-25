/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import WeilConjectures.AlgebraicGeometry.CartesianChartExchangeConclusion
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeLeg
import WeilConjectures.AlgebraicGeometry.CartesianChartRestrictedMapEvaluation

/-! # Naturality of the specified chart comparisons under exchange

Source: Stacks Project, Tag 0EYM, second proof, commutativity of its comparison square.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local irreducible] cartesianChartCohomologyIso cartesianChartRawAdjunctionIso
  cartesianChartClassPullback rawRestrictedCohomologyComparison
  abelianHigherDirectImageRawPullback

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
/-- The explicit chart lift and apex isomorphism commute with the specified
cartesian derived exchange. This asserts an identity between constructed maps;
it does not choose an isomorphism, lift, coefficient object, or representative.
Source: Stacks Project, Tags 0EYM, 03Q8, 03CB and 09YQ.
(blueprint: lem-sc-cartesian-chart-exchange-naturality).

Proof: Apply rawRestrictedCohomologyComparison_naturality to the chart cone leg
with its upperStarComp coefficient map. It identifies the inverse evaluation of
the restricted cohomology map with abelianHigherDirectImageRawPullback of the
stage class. Expand cartesianChartRawAdjunctionIso on both sides. Pullback
uniqueness identifies the two arrows from the actual apex source to the chart
stage: the inverse chart identification followed by the chart leg equals the
cartesian projection followed by the inverse stage identification. Each equality
is checked after the two pullback projections. Inverse-image composition then
identifies the coefficient maps and the free-sheaf source maps; its associativity
and naturality cancel the chart identifications. Take derived adjoints under the
apex projection. Replace derivedBaseChangeMapPlus by its mate using
baseChange_eq_derivedBaseChangeMapPlus. The adjunction triangle identity cancels
the stage counit with its unit, leaving exactly the pullback of the raw stage
class followed by the coefficient comparison. Naturality of the single-functor
and shift comparisons identifies these factors with the definition of
abelianHigherDirectImageRawPullback. Undoing the raw evaluation comparison proves
the equation. The free-sheaf source is transported by the specified pullback
square hr throughout; no invertibility of exchange is used. Empty test objects
and q=0 require no separate argument. -/
theorem cartesianChartCohomologyLift_exchange
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (U : c.pt.left.Etale)
    (r : U.left ⟶ V.left) (hr : IsPullback r U.hom V.hom (c.π.app i).left)
    (j : Over i)
    (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D i).obj j) V) :
    cartesianChartCohomologyLift f D c F q i V U r hr j x ≫
      (shiftFunctor _ (q : ℤ)).map
        (cartesianDerivedImageMap f (D.obj j.left).hom c.pt.hom
          (c.π.app j.left).left (Over.w (c.π.app j.left)).symm
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) =
    (cartesianChartCohomologyIso f (D.obj i).hom (c.π.app i).left c.pt.hom
      (Over.w (c.π.app i)).symm F q V U r hr).hom
      (restrictedOverCohomologyMap (pullback.snd f (D.obj i).hom)
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
        (q : ℤ) ((cartesianChartCone f D c i).π.app j) V x) := by
  have hl₁ : ((cartesianChartCone f D c i).π.app j).left ≫
      pullback.fst (D.map j.hom).left (pullback.snd f (D.obj i).hom) =
      pullback.fst (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
        (c.π.app j.left).left := by
    rw [cartesianChartCone_leg_eq_pullback]
    exact pullback.lift_fst _ _ _
  have hl₂ : ((cartesianChartCone f D c i).π.app j).left ≫
      pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) := by
    rw [cartesianChartCone_leg_eq_pullback]
    exact pullback.lift_snd _ _ _
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
  let z := rawRestrictedCohomologyClass h q G V x
  let z' := cartesianChartRestrictedRawClass f D c F q i V j x hl₂
  have hm := chartRawAdj_classPullback (B := (D.obj i).left)
    (T := (D.obj j.left).left) (T' := c.pt.left) f (D.obj i).hom (D.map j.hom).left
    (D.obj j.left).hom (Over.w (D.map j.hom)).symm (c.π.app j.left).left
    (c.π.app i).left (congrArg (fun t ↦ t.left) (c.w j.hom)).symm c.pt.hom
    (Over.w (c.π.app i)).symm (Over.w (c.π.app j.left)).symm
    l hl₁ hl₂ wl F q V U r hr z z'
    (cartesianChartRestrictedRawClass_eq f D c F q i V j x hl₂)
  have hR := cartesianChartRestrictedCohomologyMap_eval f D c F q i V U r hr j x hl₂
  let _ := isIso_rawRestrictedCohomologyComparison h q G V
  let e := asIso (rawRestrictedCohomologyComparison h q G V)
  have ez : z = e.inv x :=
    rawRestrictedCohomologyClass.eq_def h q G V x
  have hs₀ := congrArg
    (fun y ↦ (cartesianChartRawAdjunctionIso f (D.obj i).hom (D.map j.hom).left
      (D.obj j.left).hom (Over.w (D.map j.hom)).symm F q V).hom y) ez.symm
  have hs := congrArg
    (fun y ↦ cartesianChartClassPullback (B := (D.obj i).left)
      (T := (D.obj j.left).left) (T' := c.pt.left) (D.map j.hom).left (c.π.app j.left).left
      (c.π.app i).left (congrArg (fun t ↦ t.left) (c.w j.hom)).symm V U r hr _ (q : ℤ) y ≫
      (shiftFunctor _ (q : ℤ)).map
        (cartesianDerivedImageMap f (D.obj j.left).hom c.pt.hom
          (c.π.app j.left).left (Over.w (c.π.app j.left)).symm
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) hs₀
  exact hs.trans (hm.trans hR.symm)

end AlgebraicGeometry.Etale
