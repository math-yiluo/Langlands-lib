/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalClassEdgeMap
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSingleAdjunctionTranspose
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.CategoryTheory.LeftExactUpperTruncationComparison
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageSectionPresheaf

/-! # Normalization of the resolution edge by the derived unit
Source: Stacks Project, cohomology.tex, Tags 0BKJ and 079W.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit

private theorem complexUnit_resolutionIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (I : CochainComplex C ℤ) [I.IsKInjective] :
    F.complexDerivedUnit.app I ≫ (F.rightDerivedFunctorObjQIso I).hom = 𝟙 _ := by
  have h : F.complexDerivedUnit.app I = (F.rightDerivedFunctorObjQIso I).inv := by
    simp only [Functor.complexDerivedUnit, Functor.rightDerivedFunctorObjQIso,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom, Functor.mapIso_inv,
      Iso.symm_inv, Iso.trans_inv, Iso.app_inv, Iso.app_hom, asIso_hom, Category.assoc]
  rw [h, Iso.inv_hom_id]

private theorem single_raw_edge
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (M : C) (q : ℤ) :
    let J := (CochainComplex.singleFunctor C q).obj M
    let t := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) q).app M
    HomologicalComplex.homologyMap t.inv q ≫
      ShortComplex.leftExactHomologyEdge F (J.sc q) =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q (F.obj M)).hom ≫
        F.map (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q M).inv := by
  dsimp only
  let J := (CochainComplex.singleFunctor C q).obj M
  let B := (CochainComplex.singleFunctor D q).obj (F.obj M)
  let t := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) q).app M
  let E := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q M
  let E' := HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q (F.obj M)
  apply (cancel_mono (F.map E.hom)).1
  simp only [E, Category.assoc, ← F.map_comp, Iso.inv_hom_id,
    F.map_id, Category.comp_id]
  apply (cancel_epi (B.homologyπ q)).1
  rw [← Category.assoc, ← Category.assoc, HomologicalComplex.homologyπ_naturality,
    Category.assoc, Category.assoc]
  change HomologicalComplex.cyclesMap t.inv q ≫ (J.sc q |>.map F).homologyπ ≫
    ShortComplex.leftExactHomologyEdge F (J.sc q) ≫ F.map E.hom =
      B.homologyπ q ≫ E'.hom
  rw [ShortComplex.homologyπ_leftExactHomologyEdge_assoc]
  rw [← F.map_comp]
  change HomologicalComplex.cyclesMap t.inv q ≫
    (ShortComplex.leftExactCyclesIso F (J.sc q)).inv ≫
      F.map (J.homologyπ q ≫ E.hom) = B.homologyπ q ≫ E'.hom
  have hJ : J.homologyπ q ≫ E.hom = J.iCycles q ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) q M).hom :=
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom _ _ _
  have hB : B.homologyπ q ≫ E'.hom = B.iCycles q ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) q (F.obj M)).hom :=
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom _ _ _
  rw [hJ, hB, F.map_comp]
  change HomologicalComplex.cyclesMap t.inv q ≫
    (ShortComplex.leftExactCyclesIso F (J.sc q)).inv ≫
      F.map (J.sc q).iCycles ≫ F.map
        (HomologicalComplex.singleObjXSelf (.up ℤ) q M).hom = _
  rw [ShortComplex.leftExactCyclesIso_inv_i_assoc]
  change HomologicalComplex.cyclesMap t.inv q ≫
    ((F.mapHomologicalComplex (.up ℤ)).obj J).iCycles q ≫ _ = _
  have hi := HomologicalComplex.cyclesMap_i t.inv q
  change HomologicalComplex.cyclesMap t.inv q ≫
    ((F.mapHomologicalComplex (.up ℤ)).obj J).iCycles q =
      B.iCycles q ≫ t.inv.f q at hi
  rw [reassoc_of% hi]
  have ht : t.inv.f q =
      (HomologicalComplex.singleObjXSelf (.up ℤ) q (F.obj M)).hom ≫
        F.map (HomologicalComplex.singleObjXSelf (.up ℤ) q M).inv :=
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self F (.up ℤ) q M
  rw [ht]
  simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id]

private theorem single_homology_iso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] (M : C) (q : ℤ) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).app M =
      (DerivedCategory.homologyFunctorFactors C q).app
        ((CochainComplex.singleFunctor C q).obj M) ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q M := by
  apply Iso.ext
  simp only [DerivedCategory.singleFunctorCompHomologyFunctorIso, Iso.app_hom,
    NatIso.trans_app, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.mapIso_hom, SingleFunctors.evaluation_map,
    DerivedCategory.singleFunctorsPostcompQIso_hom_hom,
    Functor.isoWhiskerLeft_hom, Functor.comp_obj,
    Functor.id_obj, Functor.associator_hom_app, Functor.whiskerLeft_app,
    HomologicalComplex.homologyFunctorSingleIso_hom_app, Functor.whiskerRight_app,
    NatTrans.id_app, CochainComplex.singleFunctor]
  change (DerivedCategory.homologyFunctor C q).map
    (𝟙 (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C q).obj M))) ≫
      𝟙 _ ≫ _ = _
  rw [(DerivedCategory.homologyFunctor C q).map_id]
  simp only [Category.id_comp]

-- Do the naturality calculation with abstract categories, before specializing to sheaves.
private theorem resolutionEdge_unit_of_map
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (q : ℤ)
    (J I : CochainComplex C ℤ) [I.IsKInjective]
    (r : DerivedCategory.Q.obj I ≅ DerivedCategory.Q.obj J)
    (b : J ⟶ I) (hb : DerivedCategory.Q.map b = r.inv) :
    (DerivedCategory.homologyFunctor D q).map (F.complexDerivedUnit.app J) ≫
      (((DerivedCategory.homologyFunctor D q).mapIso
          (F.rightDerivedFunctor.mapIso r.symm ≪≫ F.rightDerivedFunctorObjQIso I) ≪≫
        (DerivedCategory.homologyFunctorFactors D q).app
          ((F.mapHomologicalComplex (.up ℤ)).obj I)).hom ≫
        ShortComplex.leftExactHomologyEdge F (I.sc q) ≫
        F.map ((DerivedCategory.homologyFunctor C q).mapIso r.symm ≪≫
          (DerivedCategory.homologyFunctorFactors C q).app I).inv) =
      (DerivedCategory.homologyFunctorFactors D q).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
        ShortComplex.leftExactHomologyEdge F (J.sc q) ≫
        F.map ((DerivedCategory.homologyFunctorFactors C q).inv.app J) := by
  let H := DerivedCategory.homologyFunctor D q
  let H' := DerivedCategory.homologyFunctor C q
  have hn := F.complexDerivedUnit.naturality b
  have hc : F.complexDerivedUnit.app J ≫
      (F.rightDerivedFunctor.map r.inv ≫ (F.rightDerivedFunctorObjQIso I).hom) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map b) := by
    dsimp only [Functor.comp_map] at hn
    rw [← hb, ← Category.assoc, ← hn, Category.assoc,
      complexUnit_resolutionIso, Category.comp_id]
  have ha : H.map (F.complexDerivedUnit.app J) ≫
      ((DerivedCategory.homologyFunctor D q).mapIso
          (F.rightDerivedFunctor.mapIso r.symm ≪≫ F.rightDerivedFunctorObjQIso I) ≪≫
        (DerivedCategory.homologyFunctorFactors D q).app
          ((F.mapHomologicalComplex (.up ℤ)).obj I)).hom =
      (DerivedCategory.homologyFunctorFactors _ q).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
          HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map b) q := by
    have hf := (DerivedCategory.homologyFunctorFactors _ q).hom.naturality
      ((F.mapHomologicalComplex (.up ℤ)).map b)
    dsimp only [Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.app_hom, Functor.comp_obj,
      HomologicalComplex.homologyFunctor_obj]
    change H.map _ ≫ (H.map (_ ≫ _) ≫ _) = _
    rw [← H.map_comp_assoc, hc]
    exact hf
  have he := ShortComplex.leftExactHomologyEdge_naturality F
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) q).map b)
  have hr : HomologicalComplex.homologyMap b q ≫
      ((DerivedCategory.homologyFunctor C q).mapIso r.symm ≪≫
        (DerivedCategory.homologyFunctorFactors C q).app I).inv =
      (DerivedCategory.homologyFunctorFactors _ q).inv.app J := by
    have hf := (DerivedCategory.homologyFunctorFactors _ q).inv.naturality b
    simp only [Functor.comp_map, Functor.comp_obj,
      HomologicalComplex.homologyFunctor_map] at hf
    dsimp only [Iso.trans_inv, Iso.symm_inv,
      Functor.mapIso_inv, Iso.app_inv, Functor.comp_obj,
      HomologicalComplex.homologyFunctor_obj]
    change _ ≫ (_ ≫ H'.map r.hom) = _
    rw [← Category.assoc, hf, Category.assoc, ← H'.map_comp, hb, Iso.inv_hom_id,
      H'.map_id, Category.comp_id]
  change H.map _ ≫ (_ ≫ _ ≫ _) = _
  rw [← Category.assoc, ← Category.assoc, ha, Category.assoc]
  dsimp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj,
    HomologicalComplex.homologyMap, HomologicalComplex.sc] at *
  simp only [Category.assoc]
  erw [reassoc_of% he]
  have hh := congrArg (fun z ↦
    (DerivedCategory.homologyFunctorFactors _ q).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
        ShortComplex.leftExactHomologyEdge F (J.sc q) ≫ F.map z) hr
  simpa only [Functor.map_comp, Category.assoc, HomologicalComplex.homologyMap,
    HomologicalComplex.sc] using hh

private theorem single_homology_edge
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (M : C) (q : ℤ) :
    let J := (CochainComplex.singleFunctor C q).obj M
    let t := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) q).app M
    (DerivedCategory.homologyFunctor D q).map (DerivedCategory.Q.map t.inv) ≫
      ((DerivedCategory.homologyFunctorFactors D q).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
        ShortComplex.leftExactHomologyEdge F (J.sc q) ≫
        F.map ((DerivedCategory.homologyFunctorFactors C q).inv.app J)) =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso D q).hom.app (F.obj M) ≫
        F.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso C q).inv.app M) := by
  dsimp only
  let H := DerivedCategory.homologyFunctor D q
  let J := (CochainComplex.singleFunctor C q).obj M
  let t := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) q).app M
  have hn := (DerivedCategory.homologyFunctorFactors _ q).hom.naturality t.inv
  simp only [Functor.comp_map, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_map] at hn
  change H.map (DerivedCategory.Q.map t.inv) ≫
    (DerivedCategory.homologyFunctorFactors _ q).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj J) =
    (DerivedCategory.homologyFunctorFactors _ q).hom.app
      ((CochainComplex.singleFunctor _ q).obj (F.obj M)) ≫
      HomologicalComplex.homologyMap t.inv q at hn
  rw [← Category.assoc, ← Category.assoc, hn, Category.assoc]
  have hraw := single_raw_edge F M q
  change HomologicalComplex.homologyMap t.inv q ≫
    ShortComplex.leftExactHomologyEdge F (J.sc q) = _ at hraw
  simp only [Category.assoc]
  rw [reassoc_of% hraw]
  change (DerivedCategory.homologyFunctorFactors _ q).hom.app
    ((CochainComplex.singleFunctor _ q).obj (F.obj M)) ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q (F.obj M)).hom ≫
        F.map (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) q M).inv ≫
          F.map ((DerivedCategory.homologyFunctorFactors _ q).inv.app J) =
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ q).app (F.obj M)).hom ≫
      F.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ q).app M).inv
  rw [single_homology_iso, single_homology_iso]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc]
  rfl

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

-- Specialize the abstract calculation to the fixed resolution.
private theorem resolutionEdge_unit {T S : Scheme.{u}} (g : T ⟶ S) (q : ℤ)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings T.toRingedSpace)) ℤ) :
    let F := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let H := DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
    H.map (F.complexDerivedUnit.app J) ≫
        resolutionLocalClassEdge g q (DerivedCategory.Q.obj J) =
      (DerivedCategory.homologyFunctorFactors _ q).hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj J) ≫
        ShortComplex.leftExactHomologyEdge F (J.sc q) ≫
        F.map ((DerivedCategory.homologyFunctorFactors _ q).inv.app J) := by
  let I := RingedSpace.topEdgeResolution T.toRingedSpace (DerivedCategory.Q.obj J)
  let r := RingedSpace.topEdgeResolutionIso T.toRingedSpace (DerivedCategory.Q.obj J)
  obtain ⟨b, hb⟩ := RingedSpace.exists_complex_map_into_kInjective J I r.inv
  exact resolutionEdge_unit_of_map
    (RingedSpace.moduleDirectImage g.toLRSHom.toShHom) q J I r b hb

/-- The constructed edge on a single complex is normalized by the derived unit.
Source: Stacks, Tags 0BKJ and 079W
(blueprint: lem-weil-pbc-resolution-local-class-edge-single).

Proof: Lift the inverse fixed-resolution isomorphism to a map from the single complex
into its K-injective representative. Naturality of the right-derived unit cancels the
unit on that representative. The naturality of the kernel/cokernel homology edge then
moves the resolution map through the edge; the homology factorization cancels its
inverse. On the single complex both differentials vanish, so the remaining edge is
identified with the identity on the sole coefficient by the kernel and cokernel
universal properties. The standard single/homology isomorphisms give the equation.
The calculation uses no lower bound on the chosen K-injective representative and works
for every integer degree, including negative degrees and the zero coefficient. -/
theorem resolutionLocalClassEdge_single {T S : Scheme.{u}} (g : T ⟶ S) (q : ℤ)
    (M : SheafOfModules.{u} (moduleRings T.toRingedSpace)) :
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).map
        (topEdgeSingleDirectImageMap g q M) ≫
      resolutionLocalClassEdge g q ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj M) =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).hom.app
        ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).obj M) ≫
      (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).map
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).inv.app M) := by
  let F := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
  let H := DerivedCategory.homologyFunctor.{w, u, u + 1}
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q
  let J := (CochainComplex.singleFunctor
    (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj M
  let t := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) q).app M
  have hu : topEdgeSingleDirectImageMap g q M =
      DerivedCategory.Q.map t.inv ≫ F.complexDerivedUnit.app J := by
    unfold topEdgeSingleDirectImageMap
    simp only [cast_eq]
    dsimp only [Functor.complexDerivedUnit, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    change _ = DerivedCategory.Q.map t.inv ≫ (𝟙 _ ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj J) ≫
      F.rightDerivedFunctor.map (𝟙 _))
    rw [F.rightDerivedFunctor.map_id]
    erw [Category.id_comp, Category.comp_id]
    rfl
  rw [hu, H.map_comp, Category.assoc]
  have hunit := resolutionEdge_unit g q J
  dsimp only [Functor.comp_obj, HomologicalComplex.homologyFunctor_obj] at *
  change H.map (DerivedCategory.Q.map t.inv) ≫
    (H.map (F.complexDerivedUnit.app J) ≫
      resolutionLocalClassEdge g q (DerivedCategory.Q.obj J)) = _
  rw [hunit]
  exact single_homology_edge F M q

end AlgebraicGeometry
