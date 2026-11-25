/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenDerivedStalkIso

/-! # The open derived stalk comparison on a literal representative

Source: Stacks Project, Tags 0098 and 0D5U, exact restriction and stalks.
(blueprint: lem-pc-open-derived-stalk-representative-homology).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem homology_comparison_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology]
    [(F ⋙ G).PreservesHomology] :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom := by
  let h := S.leftHomologyData
  let h₁ := (h.map F).map G
  let h₂ := h.map (F ⋙ G)
  let γ : ShortComplex.LeftHomologyMapData (𝟙 (S.map (F ⋙ G))) h₁ h₂ :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := by simp [h₁, h₂]
      commf' := by simp [h₁, h₂]
      commπ := by simp [h₁, h₂] }
  have hh := γ.homologyMap_eq
  have hh' : h₁.homologyIso.hom = h₂.homologyIso.hom := by
    simpa [γ] using (congrArg (fun k ↦ k ≫ h₂.homologyIso.hom) hh).symm
  rw [h.mapHomologyIso_eq (F ⋙ G), (h.map F).mapHomologyIso_eq G,
    h.mapHomologyIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp,
    Category.assoc]
  simp only [← G.map_comp, Iso.inv_hom_id_assoc]
  exact congrArg (fun k ↦ k ≫ G.map (F.map h.homologyIso.inv)) hh'.symm

private theorem homology_comparison_comp_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology]
    [(F ⋙ G).PreservesHomology] :
    (S.mapHomologyIso (F ⋙ G)).inv =
      G.map (S.mapHomologyIso F).inv ≫ ((S.map F).mapHomologyIso G).inv := by
  have h : S.mapHomologyIso (F ⋙ G) =
      (S.map F).mapHomologyIso G ≪≫ G.mapIso (S.mapHomologyIso F) :=
    Iso.ext (homology_comparison_comp S F G)
  rw [h]
  rfl

private theorem ordinary_representative_homology
    {C D A B E : Type*}
    [Category C] [Category D] [Category A] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian A] [Abelian B] [Abelian E]
    (R : C ⥤ D) (L : C ⥤ A) (L0 : D ⥤ B) (F : A ⥤ E) (F0 : B ⥤ E)
    [R.Additive] [L.Additive] [L0.Additive] [F.Additive] [F0.Additive]
    [R.PreservesHomology] [L.PreservesHomology] [L0.PreservesHomology]
    [F.PreservesHomology] [F0.PreservesHomology]
    [(L ⋙ F).PreservesHomology] [(L0 ⋙ F0).PreservesHomology]
    [(R ⋙ L0 ⋙ F0).PreservesHomology]
    (S : ShortComplex C) (γ : L ⋙ F ⟶ R ⋙ L0 ⋙ F0) :
    F.map (S.mapHomologyIso L).hom ≫ γ.app S.homology ≫
        (L0 ⋙ F0).map (S.mapHomologyIso R).inv ≫
        F0.map ((S.map R).mapHomologyIso L0).inv =
      ((S.map L).mapHomologyIso F).inv ≫
        ShortComplex.homologyMap (S.mapNatTrans γ) ≫
        (((S.map R).map L0).mapHomologyIso F0).hom := by
  rw [ShortComplex.homologyMap_mapNatTrans,
    homology_comparison_comp S L F,
    homology_comparison_comp_inv S R (L0 ⋙ F0),
    homology_comparison_comp_inv (S.map R) L0 F0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem complex_homology_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (i : ℤ) (K : CochainComplex C ℤ) :
    (F.mapHomologicalComplexHomologyIso (.up ℤ) i).app K =
      (K.sc i).mapHomologyIso F := by
  apply Iso.ext
  simp only [Functor.comp_obj, Functor.mapHomologicalComplexHomologyIso,
    Functor.mapHomologicalComplexCompShortComplexFunctorIso, Functor.isoWhiskerRight_refl,
    ShortComplex.homologyFunctorIso, Iso.refl_trans, NatIso.trans_app, Iso.trans_hom, Iso.app_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    HomologicalComplex.homologyFunctorIso_hom_app, Iso.symm_hom,
    Functor.associator_inv_app, Functor.associator_hom_app, NatIso.ofComponents_hom_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    HomologicalComplex.homologyFunctorIso_inv_app, Category.id_comp]
  erw [Category.id_comp, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]

private theorem exact_representative_homology
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (i : ℤ) (K : CochainComplex C ℤ) :
    (DerivedCategory.homologyFunctorFactors D i).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (DerivedCategory.homologyFunctor D i).map (F.mapDerivedCategoryFactors.inv.app K) ≫
      (F.mapDerivedCategoryHomologyFunctorIso i).inv.app (DerivedCategory.Q.obj K) =
      ((K.sc i).mapHomologyIso F).hom ≫
        F.map ((DerivedCategory.homologyFunctorFactors C i).inv.app K) := by
  apply (cancel_mono ((F.mapDerivedCategoryHomologyFunctorIso i).hom.app
    (DerivedCategory.Q.obj K))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
  simp only [← F.map_comp_assoc, Iso.inv_hom_id_app]
  erw [F.map_id, Category.id_comp]
  have he := complex_homology_iso F i K
  have he' : (F.mapHomologicalComplexHomologyIso (.up ℤ) i).inv.app K =
      ((K.sc i).mapHomologyIso F).inv := congrArg Iso.inv he
  erw [he', Iso.hom_inv_id_assoc, Category.comp_id]

private theorem exact_representative_homology_hom
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (i : ℤ) (K : CochainComplex C ℤ) :
    F.map ((DerivedCategory.homologyFunctorFactors C i).inv.app K) ≫
      (F.mapDerivedCategoryHomologyFunctorIso i).hom.app (DerivedCategory.Q.obj K) ≫
      (DerivedCategory.homologyFunctor D i).map (F.mapDerivedCategoryFactors.hom.app K) =
      ((K.sc i).mapHomologyIso F).inv ≫
        (DerivedCategory.homologyFunctorFactors D i).inv.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  rw [Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
  simp only [Category.assoc, ← F.map_comp_assoc, Iso.inv_hom_id_app,
    F.map_id, Category.id_comp, ← Functor.map_comp]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  erw [← Iso.app_inv, complex_homology_iso]

private theorem additive_stalk_representative_homology
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (Y : Scheme.{u}) (y : Y) (i : ℤ)
    (N : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    let F := forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
    let L := RingedSpace.moduleStalkFunctor Y.toRingedSpace y
    F.map (comparisonStalkHomologyIso Y y N i).inv ≫
        (additiveStalkCohomologyIso Y y i).hom.app (DerivedCategory.Q.obj N) =
      F.map ((N.sc i).mapHomologyIso L).hom ≫
        (L ⋙ F).map ((DerivedCategory.homologyFunctorFactors _ i).inv.app N) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} (Y.presheaf.stalk y))
  let F := forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  let L := RingedSpace.moduleStalkFunctor Y.toRingedSpace y
  have h := congrArg (fun k ↦ F.map k) (exact_representative_homology L i N)
  simpa only [comparisonStalkHomologyIso, additiveStalkCohomologyIso,
    Iso.trans_inv, Functor.mapIso_inv, Iso.app_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.map_comp, Category.assoc,
    Iso.app_inv, Functor.comp_map] using h

/-- On a complex, the constructed derived comparison is homology of the inverse
additive restriction-stalk map, conjugated by the exact forgetful comparisons.

Proof: expand openDerivedStalkIso and openRestrictionRepresentativeIso. Naturality
of additiveStalkCohomologyIso moves the exact-restriction localization factor to
its homology image, and the derived-restriction factors cancel. Evaluate each
mapDerivedCategoryHomologyFunctorIso on Q(N), using its hom_app_Q formula.
The localization and derived homology factors then cancel against
comparisonStalkHomologyIso at both ends. The remaining expression is the inverse
restriction-stalk natural transformation on sheaf homology, conjugated by the
exact-stalk homology comparisons. Apply ShortComplex.homologyMap_mapNatTrans to
N.sc i. The comparison for the composite stalk/forget functor equals the stalk
comparison followed by the forget comparison: compute both with the same mapped
left homology data (its kernel and cokernel). Cancel these comparisons to obtain
the formula below. This computation is valid also for zero complexes, arbitrary
homology, and identity open immersions; it uses no choice of a representative.
Source: Stacks Project, Tag 0D5U, opening paragraph; Tag 0098, stalk identification;
exact-functor homology and localization naturality.
(blueprint: lem-pc-open-derived-stalk-representative-homology). -/
theorem openDerivedStalk_representative_homology
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] (y : Y) (i : ℤ)
    (N : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ) :
    let F := forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}
    let F0 := forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
    let S := (RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)).mapHomologicalComplex
      (.up ℤ)
    let S0 := (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapHomologicalComplex
      (.up ℤ)
    let R := (Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)
    let HU := comparisonStalkCohomology Y y i ⋙ F0
    F.map (comparisonStalkHomologyIso Z (j y) N i).inv ≫
        (openDerivedStalkIso j y i).hom.app (DerivedCategory.Q.obj N) ≫
        HU.map (openRestrictionRepresentativeIso j N).inv =
      (((S.obj N).sc i).mapHomologyIso F).inv ≫
        ShortComplex.homologyMap
          ((N.sc i).mapNatTrans
            (show (RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y) ⋙ F) ⟶
              (openRestrictionFunctor j ⋙
                RingedSpace.moduleStalkFunctor Y.toRingedSpace y ⋙ F0) from
              (Scheme.Modules.restrictStalkNatIso j y).inv)) ≫
        (((S0.obj (R.obj N)).sc i).mapHomologyIso F0).hom ≫
        F0.map (comparisonStalkHomologyIso Y y (R.obj N) i).inv := by
  let := HasDerivedCategory.standard (ModuleCat.{u} (Z.presheaf.stalk (j y)))
  let := HasDerivedCategory.standard (ModuleCat.{u} (Y.presheaf.stalk y))
  dsimp only
  let F := forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}
  let F0 := forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  let L := RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)
  let L0 := RingedSpace.moduleStalkFunctor Y.toRingedSpace y
  let R := openRestrictionFunctor j
  let := comp_preservesFiniteLimits L F
  let := comp_preservesFiniteColimits L F
  let := comp_preservesFiniteLimits L0 F0
  let := comp_preservesFiniteColimits L0 F0
  let := comp_preservesFiniteLimits R (L0 ⋙ F0)
  let := comp_preservesFiniteColimits R (L0 ⋙ F0)
  have hZ' := additive_stalk_representative_homology Z (j y) i N
  have hY' := additive_stalk_representative_homology Y y i
    ((R.mapHomologicalComplex (.up ℤ)).obj N)
  simp only [openDerivedStalkIso, openRestrictionRepresentativeIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Iso.app_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
    Category.assoc]
  erw [reassoc_of% hZ']
  simp only [← Iso.app_inv, ← Iso.app_hom, Iso.inv_hom_id_map_assoc]
  have hn := (additiveStalkCohomologyIso Y y i).inv.naturality
    (R.mapDerivedCategoryFactors.hom.app N)
  simp only [Functor.comp_map] at hn
  conv_lhs => arg 2; arg 2; arg 2; arg 2; erw [← hn]
  have ht := (Scheme.Modules.restrictStalkNatIso j y).inv.naturality
    ((DerivedCategory.homologyFunctorFactors _ i).inv.app N)
  simp only [Functor.comp_map] at ht
  conv_lhs => arg 2; erw [reassoc_of% ht]
  have hr := exact_representative_homology_hom R i N
  have hr' := congrArg (fun k ↦ (L0 ⋙ F0).map k) hr
  simp only [Functor.map_comp] at hr'
  conv_lhs => arg 2; arg 2; erw [reassoc_of% hr']
  have hy : (L0 ⋙ F0).map
        ((DerivedCategory.homologyFunctorFactors _ i).inv.app
          ((R.mapHomologicalComplex (.up ℤ)).obj N)) ≫
      (additiveStalkCohomologyIso Y y i).inv.app
        (DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj N)) =
      F0.map ((((R.mapHomologicalComplex (.up ℤ)).obj N).sc i).mapHomologyIso L0).inv ≫
        F0.map (comparisonStalkHomologyIso Y y
          ((R.mapHomologicalComplex (.up ℤ)).obj N) i).inv := by
    apply (cancel_epi (F0.map
      ((((R.mapHomologicalComplex (.up ℤ)).obj N).sc i).mapHomologyIso L0).hom)).mp
    rw [← Category.assoc, ← hY']
    simp only [Category.assoc, Iso.hom_inv_id_app,
      ← F0.map_comp_assoc, Iso.hom_inv_id, F0.map_id, Category.id_comp]
    erw [Category.comp_id]
  conv_lhs => arg 2; arg 2; arg 2; erw [hy]
  have h := congrArg (fun k ↦ k ≫ F0.map (comparisonStalkHomologyIso Y y
    ((R.mapHomologicalComplex (.up ℤ)).obj N) i).inv)
    (ordinary_representative_homology R L L0 F F0 (N.sc i)
      (show (L ⋙ F) ⟶ (R ⋙ L0 ⋙ F0) from
        (Scheme.Modules.restrictStalkNatIso j y).inv))
  simp only [Category.assoc] at h
  exact h

end AlgebraicGeometry.SingleComplexBaseChange
