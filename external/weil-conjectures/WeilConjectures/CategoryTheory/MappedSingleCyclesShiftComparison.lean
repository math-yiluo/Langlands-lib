/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
import WeilConjectures.CategoryTheory.SingleHomologyShiftComparison

/-!
# Canonical single-complex shift comparisons

These comparisons isolate the source and unit transport calculations used by
`rightDerivedFunctorPlusUnit_canonical_single_shift`.
-/

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory C]
  (G : B ⥤ C) [G.Additive]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Cycles comparison for the mapped single complex after shift.

Source: Stacks Project, derived.tex, Tag 015J, proof remark (1), and the
canonical single-functor, quotient and homology shift comparisons.
(blueprint: lem-pc-mapped-single-cycles-shift-comparison)

Proof: Expand mapHomotopyCategoryPlusSingleFunctorQhObjIso and use naturality
of homologyFunctorObjQIso to replace its homology map by homologyMap of the
singleMapHomologicalComplex coefficient isomorphism. Naturality of homologyπ
then identifies the source map with iCycles followed by the mapped sole-term
coefficient identification and the inverse single-object homology comparison
in degree n. The inverse single-functor shift isomorphism carries the sole term
from n to zero, while H₀.shiftIso identifies the resulting homology in degree n
with degree-zero homology. Both comparisons are induced by the identity on the
sole nonzero coefficient, so their composite takes the inverse degree-n single
homology comparison to singleFunctorCompHomologyFunctorIso 0 inverse. This gives
the displayed equality. The shift sign occurs only in the differential, which
is zero for a single complex; n=0 uses the shift unit laws and X=0 uses the
same natural maps. No right-derived unit or enough-injectives argument is used. -/
theorem mappedSingle_cycles_shift_comparison (X : B) (n : ℕ) :
    let S : CochainComplex.Plus B :=
      ⟨(CochainComplex.singleFunctor B (n : ℤ)).obj X, n, inferInstance⟩
    let GS := G.mapCochainComplexPlus.obj S
    let H₀ := DerivedCategory.Plus.homologyFunctor C 0
    let d := Functor.isoWhiskerRight
      ((DerivedCategory.Plus.singleFunctors C).shiftIso (-(n : ℤ)) n 0 (by simp)).symm
      (H₀.shift (n : ℤ)) ≪≫
      Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
        (H₀.shiftIso (-(n : ℤ)) (n : ℤ) 0 (by ring))
    GS.obj.homologyπ n ≫ (DerivedCategory.Plus.homologyFunctorObjQIso GS n).inv ≫
      (DerivedCategory.Plus.homologyFunctor C n).map
        ((DerivedCategory.Plus.quotientCompQhIso C).inv.app GS) ≫
      (DerivedCategory.Plus.homologyFunctor C n).map
        (G.mapHomotopyCategoryPlusSingleFunctorQhObjIso n X).hom ≫
      d.hom.app (G.obj X) =
    GS.obj.iCycles n ≫
      G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n X).hom ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app (G.obj X) := by
  dsimp only
  let S : CochainComplex.Plus B :=
    ⟨(CochainComplex.singleFunctor B (n : ℤ)).obj X, n, inferInstance⟩
  let GS := G.mapCochainComplexPlus.obj S
  let SC : CochainComplex.Plus C :=
    ⟨(CochainComplex.singleFunctor C (n : ℤ)).obj (G.obj X), n, inferInstance⟩
  let p : GS ⟶ SC := ObjectProperty.homMk
    ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) n).hom.app X)
  apply (cancel_mono
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).hom.app (G.obj X))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [singleFunctor_homology_shift_comparison (G.obj X) (n : ℤ)]
  have hmap : (DerivedCategory.Plus.quotientCompQhIso C).inv.app GS ≫
      (G.mapHomotopyCategoryPlusSingleFunctorQhObjIso n X).hom =
      DerivedCategory.Plus.Q.map p := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.map_comp, mapHomotopyCategoryPlusSingleFunctorQhObjIso,
      Functor.preimageIso_hom, Functor.map_preimage, Functor.mapIso_hom,
      Iso.trans_hom, Iso.app_hom]
    change (DerivedCategory.quotientCompQhIso C).inv.app GS.obj ≫
      (DerivedCategory.quotientCompQhIso C).hom.app GS.obj ≫
        DerivedCategory.Q.map p.hom = DerivedCategory.Q.map p.hom
    simp
  rw [← Functor.map_comp_assoc, hmap]
  have hsingle :
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).inv.app (G.obj X) ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso SC n).hom =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n (G.obj X)).inv := by
    simp only [Functor.id_obj, Functor.comp_obj,
      DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso,
      DerivedCategory.singleFunctorCompHomologyFunctorIso,
      HomologicalComplex.homologyFunctorSingleIso, Iso.trans_inv,
      Functor.isoWhiskerLeft_inv, Category.assoc, Functor.isoWhiskerRight_inv,
      Functor.mapIso_inv, SingleFunctors.evaluation_map, NatTrans.comp_app,
      NatIso.ofComponents_inv_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Category.id_comp,
      DerivedCategory.Plus.homologyFunctorObjQIso,
      Iso.app_hom, SC]
    rw [DerivedCategory.singleFunctorsPostcompQIso_inv_hom]
    simp
  have hsingle' : (DerivedCategory.Plus.homologyFunctorObjQIso SC n).inv ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).hom.app (G.obj X) =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) n (G.obj X)).hom := by
    apply (cancel_mono
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso n).inv.app (G.obj X))).1
    simp only [Category.assoc, Iso.hom_inv_id_app]
    apply (cancel_mono (DerivedCategory.Plus.homologyFunctorObjQIso SC n).hom).1
    simp only [Category.assoc]
    erw [Category.id_comp, Iso.inv_hom_id]
    rw [hsingle]
    simp
  have hnat := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality p (n : ℤ)
  have hnat' : (DerivedCategory.Plus.homologyFunctorObjQIso GS n).inv ≫
      (DerivedCategory.Plus.homologyFunctor C n).map (DerivedCategory.Plus.Q.map p) =
      HomologicalComplex.homologyMap p.hom n ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso SC n).inv := by
    apply (cancel_mono (DerivedCategory.Plus.homologyFunctorObjQIso SC n).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hnat]
    simp
  rw [reassoc_of% hnat', hsingle', HomologicalComplex.homologyπ_naturality_assoc]
  erw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom, ← Category.assoc,
    HomologicalComplex.cyclesMap_i, Category.assoc]
  dsimp only [p, ObjectProperty.homMk_hom]
  rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  simp only [Functor.id_obj, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory.Functor
