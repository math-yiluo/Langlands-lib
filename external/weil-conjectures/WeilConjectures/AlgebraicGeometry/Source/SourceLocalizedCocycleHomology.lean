/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceComparison

/-! # Evaluation of a localized cocycle on the cohomology sheaf

Source: Stacks Project, Tag 03Q8, computation with an injective complex.
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.SourceLocalizedCocycleHomology.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry CochainComplex CochainComplex.HomComplex

namespace AlgebraicGeometry.Etale

/-- The homology section of a cocycle, evaluated at the free generator.
This construction uses the actual cycle map and transports homology along `r`.
Source: Stacks Project, Tag 03Q8.
(blueprint: lem-weil-pbc-source-localized-cocycle-homology). -/
noncomputable def smallModel_sourceCocycleHomologySection {S : Scheme.{v}}
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) (W : S.Etale)
    (f : (strictLocalFreeSheaf S.smallEtaleTopology).obj W ⟶ L.X n)
    (hf : f ≫ L.d n (n + 1) = 0) :
    ((DerivedCategory.Plus.homologyFunctor _ n).obj K).obj.obj (op W) :=
  smallModel_sourceFreeSectionsEquiv W _
    (L.liftCycles f (n + 1) (by simp) hf ≫ L.homologyπ n ≫
      (DerivedCategory.homologyFunctorFactors _ n).inv.app L ≫
      (DerivedCategory.homologyFunctor _ n).map r.inv)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a localized single-source cocycle is its actual homology section.
This is a comparison on the base site, before taking stalks or restricting to any scheme.

Source: Stacks Project, Tag 03Q8, injective-complex computation.
(blueprint: lem-weil-pbc-source-localized-cocycle-homology).

Proof: the localization isomorphism sends the class of the single-source cocycle to
its chain map into the shifted complex, then applies the quotient and shift comparison.
Degree-zero homology of that map is the map on cycles followed by the homology quotient.
The single-complex homology identification removes the source single complex. The homology
shift comparison identifies the target with degree n homology of L. Naturality of the
localization factorization and the homology shift comparison transports this equality
along r inverse. Evaluation of the resulting sheaf morphism at the free generator is
smallModel_sourceFreeSectionsEquiv, giving the displayed section. This works for every integer n;
zero cocycles give zero sections and boundaries give zero homology sections. -/
theorem smallModel_sourceLocalizedCocycleHomology {S : Scheme.{v}}
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (L : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    [L.IsKInjective] (r : K.obj ≅ DerivedCategory.Q.obj L) (n : ℤ) (W : S.Etale)
    (f : (strictLocalFreeSheaf S.smallEtaleTopology).obj W ⟶ L.X n)
    (hf : f ≫ L.d n (n + 1) = 0) :
    (strictLocalCohomologyGermMap K n).app (op W)
      ((smallModel_sourcePlusHomIso ((strictLocalFreeSheaf S.smallEtaleTopology).obj W)
        K L r n).inv
        ((smallModel_sourceClassDerivedHomIso ((strictLocalFreeSheaf S.smallEtaleTopology).obj W)
          L n).hom (CohomologyClass.mk
            (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)))) =
      smallModel_sourceCocycleHomologySection K L r n W f hf := by
  let A := (strictLocalFreeSheaf S.smallEtaleTopology).obj W
  let x := (smallModel_sourcePlusHomIso A K L r n).inv
    ((smallModel_sourceClassDerivedHomIso A L n).hom
      (CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)))
  change (((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso n 0 n
    (add_zero n)).hom.app K).hom.app (op W)
    (smallModel_sourceFreeSectionsEquiv W _
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A ≫
        (DerivedCategory.Plus.homologyFunctor _ 0).map x)) = _
  rw [← smallModel_sourceFreeSectionsEquiv_comp]
  apply congrArg (smallModel_sourceFreeSectionsEquiv W _)
  let z : Cocycle ((HomologicalComplex.single _ (.up ℤ) 0).obj A) L n :=
    Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf
  let g := Cocycle.equivHomShift.symm z
  -- Forget the bounded-below inclusion and compute localization on a cocycle.
  have hplus : DerivedCategory.Plus.ι.map x =
      (smallModel_sourceClassDerivedHomIso A L n).hom (CohomologyClass.mk z) ≫
        (CategoryTheory.shiftFunctor _ n).map r.inv ≫
          (DerivedCategory.Plus.ι.commShiftIso n).inv.app K := by
    dsimp only [x, smallModel_sourcePlusHomIso, AddEquiv.mk', Iso.homCongr]
    dsimp only [AddEquiv.toAddCommGrpIso, AddEquiv.trans, AddEquiv.symm,
      AddEquiv.toAddMonoidHom, Equiv.trans, Equiv.symm, Iso.trans_inv,
      Functor.mapIso_inv, Iso.refl_hom]
    simp only [Category.id_comp]
    exact (Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.Plus.ι
        (C := Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}))).map_preimage _
  have hclass : (smallModel_sourceClassDerivedHomIso A L n).hom (CohomologyClass.mk z) =
      DerivedCategory.Q.map g ≫ (DerivedCategory.Q.commShiftIso n).hom.app L := by
    dsimp [smallModel_sourceClassDerivedHomIso, AddEquiv.mk', Iso.homCongr,
      AddEquiv.toAddCommGrpIso, AddEquiv.trans, AddEquiv.toAddMonoidHom,
      Equiv.trans, Equiv.ofBijective, AddMonoidHom.mk',
      CohomologyClass.homAddEquiv, AddEquiv.ofBijective, Functor.mapAddHom]
    erw [CohomologyClass.toHom_mk]
    simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom,
      NatTrans.id_app, Category.id_comp]
    erw [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
    erw [Iso.inv_hom_id_app_assoc]
  -- Cancel the inclusion shift comparison and move r inverse past the homology shift.
  have hs : ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso n 0 n
      (add_zero n)).hom.app K =
      (DerivedCategory.homologyFunctor _ 0).map
        ((DerivedCategory.Plus.ι.commShiftIso n).hom.app K) ≫
      ((DerivedCategory.homologyFunctor _ 0).shiftIso n 0 n
        (add_zero n)).hom.app K.obj := by
    refine (Category.id_comp _).trans ?_
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app]
    erw [Category.id_comp]
    rfl
  change (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app A ≫
    (DerivedCategory.homologyFunctor _ 0).map (DerivedCategory.Plus.ι.map x) ≫
      ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso n 0 n
        (add_zero n)).hom.app K = _
  rw [hs, hplus, hclass]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (DerivedCategory.homologyFunctor _ 0).map_comp_assoc
    ((DerivedCategory.Plus.ι.commShiftIso n).inv.app K)
    ((DerivedCategory.Plus.ι.commShiftIso n).hom.app K), Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [(DerivedCategory.homologyFunctor _ 0).shiftIso_hom_naturality
    n 0 n (add_zero n) r.inv]
  rw [← Functor.map_comp_assoc]
  change (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app A ≫
    (DerivedCategory.homologyFunctor _ 0).shiftMap (ShiftedHom.map g DerivedCategory.Q)
      0 n (add_zero n) ≫ (DerivedCategory.homologyFunctor _ n).map r.inv = _
  rw [DerivedCategory.shiftMap_homologyFunctor_map_Q g 0 n (add_zero n)]
  -- Remove the single source, leaving ordinary homology of the chain map.
  have hsingle : (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.app A ≫
      (DerivedCategory.homologyFunctorFactors _ 0).hom.app
        ((CochainComplex.singleFunctor _ 0).obj A) =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A).inv := by
    simp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
      DerivedCategory.singleFunctorsPostcompQIso_inv_hom]
  simp only [Category.assoc]
  rw [← Category.assoc]
  erw [hsingle]
  suffices h : (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A).inv ≫
      (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).shiftMap g 0 n (add_zero n) =
      L.liftCycles f (n + 1) (by simp) hf ≫ L.homologyπ n by
    simpa only [Category.assoc] using congrArg
      (fun t ↦ t ≫ (DerivedCategory.homologyFunctorFactors _ n).inv.app L ≫
        (DerivedCategory.homologyFunctor _ n).map r.inv) h
  -- The chain map lifts its degree-zero component to cycles of the shifted complex.
  let a := (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).inv ≫ g.f 0
  have ha : a ≫ (L⟦n⟧).d 0 1 = 0 := by
    dsimp only [a]
    rw [Category.assoc, g.comm]
    simp [HomologicalComplex.single_obj_d]
  have hcycle : (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0 A).inv ≫
      HomologicalComplex.cyclesMap g 0 = (L⟦n⟧).liftCycles a 1 (by simp) ha := by
    apply (cancel_mono ((L⟦n⟧).iCycles 0)).1
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc,
      HomologicalComplex.liftCycles_i]
    rfl
  change (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A).inv ≫
    HomologicalComplex.homologyMap g 0 ≫
      ((HomologicalComplex.homologyFunctor _ (.up ℤ) 0).shiftIso n 0 n
        (add_zero n)).hom.app L = _
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ,
    Category.assoc, HomologicalComplex.homologyπ_naturality_assoc]
  rw [← Category.assoc, hcycle]
  rw [CochainComplex.liftCycles_shift_homologyπ_assoc L a 1 (by simp) ha n
    (add_zero n) (n + 1) (by simp)]
  simp only [Iso.inv_hom_id_app]
  erw [Category.comp_id]
  -- Unshifting this component recovers the original cycle f.
  have hcomponent : a ≫ (L.shiftFunctorObjXIso n 0 n (by simp)).hom = f := by
    dsimp only [a, g, z, Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f,
      Cocycle.rightShift_coe]
    erw [(Cochain.fromSingleMk f (zero_add n)).rightShift_v
      n 0 (zero_add n) 0 0 (by simp) n (zero_add n)]
    erw [Cochain.fromSingleMk_v]
    simp [Category.assoc]
  simp only [hcomponent]

end AlgebraicGeometry.Etale
