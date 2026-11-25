/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison

/-! # The bottom Grothendieck edge and the derived unit

Source: Stacks Project, Derived Categories, Tags 015N and 015J.
(blueprint: lem-sc-grothendieck-bottom-edge-single-unit)
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The raw bottom edge, with its source identified, is homology of the derived unit.
Source: Stacks Project, Derived Categories, Tags 015N and 015J, bottom interval.
(blueprint: lem-sc-grothendieck-bottom-edge-single-unit).

Proof: Put R = RF(X). It has no negative homology. The left exactness of F implies
that the degree-zero homology of the unit F(X)[0] to R is invertible. Specifically,
under singleFunctorCompHomologyFunctorIso and the single-object derived homology
comparison, this map is toRightDerivedZero, by
rightDerivedPlusSingleUnitHomology_comp_comparison. Its inverse is exactly the
rightDerivedZeroIsoSelf factor in grothendieckBottomEdgeSourceIso.
Since F(X)[0] has no positive homology, the unit factors uniquely through truncation
below 1 of R. Since R has no negative homology, this truncation lies in degree zero,
and its further truncation at degrees at least zero is isomorphic to itself.
The canonical eTruncLTCompETruncGEIso identifies this bottom interval with H^0(R)[0].
The degree-zero homology equality just established therefore identifies the inverse
source isomorphism followed by the interval inclusion with the derived unit.
Expand grothendieckSpectralObjectHIso at q = 0: the zero shifts of the single functor,
RG, and homology cancel by their shift-zero coherence identities. Naturality of the
single-object derived homology comparison for G moves the inverse H^0 identification
through R^nG. Thus applying RG and H^n to the interval inclusion gives the displayed
map, with the inverse single-object comparison for G as its only source factor.
This uses neither an injective resolution comparison nor composite acyclicity.
For n = 0 the same interval inclusion applies; for zero objects or zero functors both
sides are zero. No assumption that G is left exact is used.
-/
theorem grothendieckBottomEdge_singleUnit
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] (X : A) (n : ℕ) :
    (F.grothendieckBottomEdgeSourceIso G n).inv.app X ≫
        (F.grothendieckBottomEdge G n).app X =
      (G.homologyRightDerivedFunctorPlusObjSingleFunctorIso (F.obj X) n).inv ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          (G.rightDerivedFunctorPlus.map (F.rightDerivedPlusSingleUnit X)) := by
  have hzero :
      (F.grothendieckSpectralObjectHIso G n 0 n 0 1 (by simp) (by simp) (by simp)).hom.app X =
        (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.eTruncLTCompETruncGEIso 0).hom.app
            (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)))) ≫
        (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n).hom.app
          ((DerivedCategory.Plus.homologyFunctor B 0).obj
            (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))) ≫
        (G.rightDerived n).map
          ((F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).hom.app X) := by
    have h := F.grothendieckSpectralObjectHIso_hom_app G n 0 X
    simp only [Nat.add_zero, Int.natCast_zero] at h
    erw [h]
    erw [SingleFunctors.shiftIso_zero_inv_app, Functor.commShiftIso_zero,
      Functor.CommShift.isoZero_hom_app, Functor.shiftIso_zero_hom_app]
    simp only [← Functor.map_comp_assoc]
    simp only [homOfLE_leOfHom, Functor.comp_obj, Int.reduceAdd,
      Triangulated.TStructure.eTruncLT_obj_coe, Triangulated.TStructure.eTruncGE_obj_coe,
      Int.neg_zero, Iso.inv_hom_id_app, Functor.id_obj, Category.comp_id,
      Functor.map_comp, Category.assoc, Int.cast_ofNat_Int]
    erw [← (DerivedCategory.Plus.homologyFunctor C n).map_comp_assoc
      ((shiftFunctorZero (DerivedCategory.Plus C) ℤ).inv.app _)
      ((shiftFunctorZero (DerivedCategory.Plus C) ℤ).hom.app _)]
    simp
  have hinterval (K : DerivedCategory.Plus B) [K.IsGE 0] (M : B)
      (u : (DerivedCategory.Plus.singleFunctor B 0).obj M ⟶ K) :
      (DerivedCategory.Plus.singleFunctor B 0).map
          ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app M ≫
            (DerivedCategory.Plus.homologyFunctor B 0).map u) ≫
        (DerivedCategory.Plus.eTruncLTCompETruncGEIso 0).inv.app K ≫
        inv ((DerivedCategory.Plus.TStructure.t.truncGEπ 0).app
          ((DerivedCategory.Plus.TStructure.t.truncLT 1).obj K)) ≫
        (DerivedCategory.Plus.TStructure.t.truncLTι 1).app K = u := by
    let t := DerivedCategory.Plus.TStructure.t (C := B)
    let l := t.liftTruncLT u 0 1 (by simp)
    have h : (DerivedCategory.Plus.singleFunctor B 0).map
          ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app M ≫
            (DerivedCategory.Plus.homologyFunctor B 0).map u) =
        l ≫ (t.truncGEπ 0).app ((t.truncLT 1).obj K) ≫
          (DerivedCategory.Plus.eTruncLTCompETruncGEIso 0).hom.app K := by
      apply DerivedCategory.Plus.singleFunctor_hom_ext_of_isGE_of_isLE 0
      apply (cancel_mono ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).hom.app
        ((DerivedCategory.Plus.homologyFunctor B 0).obj K))).1
      erw [(DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).hom.naturality]
      simp only [Functor.id_map]
      simp only [Functor.map_comp, Category.assoc]
      erw [DerivedCategory.Plus.homologyFunctor_map_eTruncLTCompETruncGEIso_hom_app]
      erw [IsIso.hom_inv_id_assoc]
      erw [← Functor.map_comp]
      simp only [Functor.id_obj, Functor.comp_obj, Iso.hom_inv_id_app_assoc,
        Int.reduceAdd, Triangulated.TStructure.eTruncLT_obj_coe,
        Triangulated.TStructure.eTruncLT_map_eq_truncLTι, Functor.map_comp]
      exact (by simpa only [l, t.liftTruncLT_ι] using
        (DerivedCategory.Plus.homologyFunctor B 0).map_comp l ((t.truncLTι 1).app K))
    rw [h]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    have : IsIso ((t.truncGEπ 0).app ((t.truncLT 1).obj K)) :=
      inferInstance
    simp [l, t]
  have hbottom :
      (F.grothendieckBottomEdge G n).app X =
        (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlus.map
          (inv ((DerivedCategory.Plus.TStructure.t.truncGEπ 0).app
            ((DerivedCategory.Plus.TStructure.t.truncLT 1).obj
              (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)))) ≫
            (DerivedCategory.Plus.TStructure.t.truncLTι 1).app
              (F.rightDerivedFunctorPlus.obj
                ((DerivedCategory.Plus.singleFunctor A 0).obj X)))) := by
    dsimp [Functor.grothendieckBottomEdge, Abelian.SpectralObject.bottomEdge,
      Functor.grothendieckSpectralObject,
      Functor.grothendieckSpectralObjectFunctor, Functor.mapHomologicalSpectralObject,
      Triangulated.SpectralObject.mapHomologicalFunctor, Functor.mapTriangulatedSpectralObject,
      Triangulated.SpectralObject.mapTriangulatedFunctor,
      Triangulated.TStructure.spectralObjectFunctor, Triangulated.TStructure.spectralObject,
      Triangulated.TStructure.ω₁]
    simp only [homOfLE_leOfHom, Fin.isValue, Functor.map_id, NatTrans.hcomp_app,
      NatTrans.id_app]
    dsimp
    simp only [Category.id_comp, Functor.map_id, Category.comp_id]
    change inv ((DerivedCategory.Plus.homologyFunctor C n).map
      (G.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.TStructure.t.truncGEπ 0).app
        ((DerivedCategory.Plus.TStructure.t.truncLT 1).obj
          (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)))))) ≫
      (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.TStructure.t.truncLTι 1).app
          (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)))) = _
    simp
  let K := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  let H := DerivedCategory.Plus.homologyFunctor C (n : ℤ)
  let R := G.rightDerivedFunctorPlus
  let c := G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n
  have hsource : (F.grothendieckBottomEdgeSourceIso G n).inv.app X =
      (G.rightDerived n).map (F.rightDerivedPlusSingleUnitHomology X) ≫
        c.inv.app ((DerivedCategory.Plus.homologyFunctor B 0).obj K) ≫
        H.map (R.map ((DerivedCategory.Plus.eTruncLTCompETruncGEIso 0).inv.app K)) := by
    apply (cancel_mono ((F.grothendieckBottomEdgeSourceIso G n).hom.app X)).1
    simp only [Iso.inv_hom_id_app]
    simp only [Functor.grothendieckBottomEdgeSourceIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    erw [hzero]
    simp only [Category.assoc]
    erw [← H.map_comp_assoc, ← R.map_comp, Iso.inv_hom_id_app,
      R.map_id, H.map_id, Category.id_comp]
    dsimp only [c]
    erw [Iso.inv_hom_id_app_assoc]
    erw [← (G.rightDerived n).map_comp_assoc,
      F.rightDerivedPlusSingleUnitHomology_comp_comparison]
    simp [Functor.rightDerivedZeroIsoSelf]
  rw [hsource, hbottom]
  simp only [Category.assoc]
  erw [← H.map_comp, ← R.map_comp]
  have hnat := c.inv.naturality (F.rightDerivedPlusSingleUnitHomology X)
  dsimp only [Functor.comp_map] at hnat
  erw [← Category.assoc, hnat]
  simp only [Category.assoc]
  erw [← H.map_comp, ← R.map_comp]
  congr 3
  exact hinterval K (F.obj X) (F.rightDerivedPlusSingleUnit X)

end CategoryTheory
