/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import WeilConjectures.AlgebraicGeometry.RawDerivedClassAffineDescent

/-! # Finite-stage data for a raw cartesian class

Source: Stacks Project, Tags 0EYL, 0EYM and 0GIT.
(blueprint: lem-sc-cartesian-raw-class-chart-data).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local irreducible] restrictedOverCohomologyMap
  cartesianDerivedImageMap cartesianChartCohomologyLift cartesianChartCohomologyIso
  upperStar upperStarCompDerivedPlus cartesianChartRawAdjunctionIso
  rawRestrictedCohomologyComparison

set_option backward.isDefEq.respectTransparency true

private theorem chartClassPullback_postcomp {B T T' : Scheme.{u}}
    (a : T ⟶ B) (b : T' ⟶ T) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (W : B.Etale) (V : T'.Etale) (r : V.left ⟶ W.left)
    (hr : IsPullback r V.hom W.hom a')
    (K L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ)
    (y : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj W)) ⟶ K⟦q⟧)
    (e : K ⟶ L) :
    cartesianChartClassPullback a b a' ha W V r hr K q y ≫
        (shiftFunctor _ q).map ((D+((b)^*[AddCommGrpCat.{u + 1}])).map e) =
      cartesianChartClassPullback a b a' ha W V r hr L q
        (y ≫ (shiftFunctor _ q).map e) := by
  simp only [cartesianChartClassPullback, Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality]

/-- Stage exchange turns a raw finite-stage representative into a chart class.

Source: Stacks Project, Tags 0EYL and 0GIT for raw descent; Tag 0EYM for exchange.
(blueprint: lem-sc-cartesian-raw-class-chart-data).

Proof: Descend the original raw class while keeping its bounded-below coefficient
complex fixed. Postcompose the resulting finite-stage class with stage exchange.
Apply the inverse chart adjunction, then raw cohomology evaluation, to define x.
Naturality of the shift comparison shows that pullback of chart classes commutes
with postcomposition. Cancel the evaluation and adjunction isomorphisms to obtain
the base-stage identity. This constructs x explicitly from the descended class;
no class is chosen from a mere existence theorem inside a definition.
-/
theorem exists_cartesianRawClass_chart_data
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (i : I) (V : c.pt.left.Etale) [IsAffine V.left]
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree c.pt.left).obj V) ⟶
        ((D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj
          (cartesianDerivedImage f (D.obj i).hom
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧) :
    ∃ (j : I) (W : (D.obj j).left.Etale) (_ : IsAffine W.left)
      (r : V.left ⟶ W.left)
      (hr : IsPullback r V.hom W.hom (c.π.app j).left)
      (l : Over j) (b : l.left ⟶ i)
      (x : restrictedOverCohomology (pullback.snd f (D.obj j).hom)
        (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
        (q : ℤ) ((cartesianChartDiagram f D j).obj l) W),
      z ≫ (shiftFunctor _ (q : ℤ)).map
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
            (c.π.app l.left).left (D.map b).left (c.π.app i).left
            (congrArg (fun t ↦ t.left) (c.w b)).symm).hom.app _ ≫
            (D+(((c.π.app l.left).left)^*[AddCommGrpCat.{u + 1}])).map
              (cartesianDerivedImageMap f (D.obj i).hom (D.obj l.left).hom
                (D.map b).left (Over.w (D.map b)).symm
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) =
        cartesianChartCohomologyLift f D c F q j W V r hr l x := by
  obtain ⟨j, W, hW, r, hr, l, b, y, hy⟩ :=
    exists_rawDerivedClass_affine_descent D c hc q i V
      (cartesianDerivedImage f (D.obj i).hom
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) z
  let E := cartesianDerivedImageMap f (D.obj i).hom (D.obj l.left).hom
    (D.map b).left (Over.w (D.map b)).symm
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  let A := cartesianChartRawAdjunctionIso f (D.obj j).hom (D.map l.hom).left
    (D.obj l.left).hom (Over.w (D.map l.hom)).symm F q W
  let h := pullback.snd ((D.map l.hom).left) (pullback.snd f (D.obj j).hom) ≫
    pullback.snd f (D.obj j).hom
  let G := (((pullback.snd ((D.map l.hom).left)
    (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj
      (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
  let _ := isIso_rawRestrictedCohomologyComparison h q G W
  let v := y ≫ (shiftFunctor _ (q : ℤ)).map E
  let x : restrictedOverCohomology (pullback.snd f (D.obj j).hom)
      (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D j).obj l) W :=
    (rawRestrictedCohomologyComparison h q G W) (A.inv v)
  refine ⟨j, W, hW, r, hr, l, b, x, ?_⟩
  rw [Functor.map_comp, ← Category.assoc, hy]
  rw [chartClassPullback_postcomp]
  unfold cartesianChartCohomologyLift
  congr 1
  symm
  change A.hom ((asIso (rawRestrictedCohomologyComparison h q G W)).inv
    ((rawRestrictedCohomologyComparison h q G W) (A.inv v))) = v
  change A.hom ((asIso (rawRestrictedCohomologyComparison h q G W)).inv
    ((asIso (rawRestrictedCohomologyComparison h q G W)).hom (A.inv v))) = v
  rw [Iso.hom_inv_id_apply, Iso.inv_hom_id_apply]

end AlgebraicGeometry.Etale
