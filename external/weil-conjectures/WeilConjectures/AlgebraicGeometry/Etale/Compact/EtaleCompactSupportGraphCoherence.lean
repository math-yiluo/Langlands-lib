/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import all WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekBaseChange
import all WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenCompositionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Coherence of the specified compact-support graph map

Source: SGA 4 XVII 5.2.2, 6.2.11; Stacks Project Tags 03S6, 0F7B and 0F7C
(blueprint: lem-asd-compact-support-graph-coherence).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive

attribute [local irreducible] upperStar lowerStar
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor

private lemma transported_transpose_of_section
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R R' : D ⥤ C} {S : C ⥤ D}
    (adj : L ⊣ R) (adj' : R ⊣ S) [IsIso adj'.counit]
    (e : R ≅ R') (M : C) (t : M ⟶ R.obj (S.obj M))
    (ht : t ≫ adj'.counit.app M = 𝟙 M) :
    (((adj.ofNatIsoRight e).ofNatIsoRight e.symm).homEquiv M (S.obj M)).symm t =
      L.map (inv (adj'.counit.app M)) ≫ adj.counit.app (S.obj M) := by
  have he : t = inv (adj'.counit.app M) := by
    apply (cancel_mono (adj'.counit.app M)).1
    rw [ht, IsIso.inv_hom_id]
  rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply,
    Adjunction.homEquiv_ofNatIsoRight_symm_apply]
  simp only [Iso.symm_inv, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [he, Adjunction.homEquiv_counit]

private theorem graph_open_sheaf_normalization
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}}
    (k : U ⟶ X) [IsOpenImmersion k] (c : Compactification k)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleCompactificationGraphMap A k c).app M ≫
      (compactificationSheafToDirectImage A c).app M =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app M := by
  rw [compactSupportGraphSheafComparison_normalization]
  let B := ModuleCat.{u + 1} A
  have ht := transported_transpose_of_section
    (openImmersionLowerShriekAdjunction B k)
    (openImmersionRestrictionLowerStarAdjunction B k)
    (upperStarIsoLocalizationRestriction B k inferInstance).symm M
    ((lowerStarUnit B k).app M) (congr_app (lowerStarUnit_comp_counit B k) M)
  rw [openImmersionLowerShriekToLowerStar_app]
  simp only [etaleLowerShriekToLowerStar, etaleLowerShriekRestrictionAdjunction,
    etaleLowerShriekUpperStarAdjunction, openImmersionLowerShriekAdjunction,
    localizationLowerShriekAdjunction, etaleLowerShriek, openImmersionLowerShriek,
    localizationLowerShriek, Scheme.smallEtaleTopology, B, Iso.symm_symm_eq,
    NatIso.isIso_inv_app] at ht ⊢
  convert ht using 1

private lemma mono_comp_iso
    {C : Type*} [Category C] {X Y Z : C} (a : X ⟶ Y) (ha : Mono a) (e : Y ≅ Z) :
    Mono (a ≫ e.hom) := by
  let := ha
  exact mono_comp a e.hom

private theorem graph_identity_sheaf
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    etaleCompactificationGraphMap A (𝟙 X) (Compactification.ofIsProper (𝟙 X)) =
      (Functor.rightUnitor
        (etaleLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) inferInstance)).inv ≫
      Functor.whiskerLeft
        (etaleLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) inferInstance)
        (lowerStarId (ModuleCat.{u + 1} A) X).inv := by
  apply NatTrans.ext
  funext M
  have : Mono ((openImmersionLowerShriekToLowerStar
      (ModuleCat.{u + 1} A) (𝟙 X)).app M) := open_compare_mono.{u} A (𝟙 X) M
  have : Mono ((compactificationSheafToDirectImage A
      (Compactification.ofIsProper (𝟙 X))).app M) := by
    dsimp only [compactificationSheafToDirectImage, NatTrans.comp_app,
      Functor.whiskerRight_app]
    have : Mono ((lowerStar (ModuleCat.{u + 1} A) (𝟙 X)).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) (𝟙 X)).app M)) :=
      Functor.map_mono (lowerStar (ModuleCat.{u + 1} A) (𝟙 X)) _
    dsimp only [Compactification.ofIsProper]
    exact mono_comp_iso
      ((lowerStar (ModuleCat.{u + 1} A) (𝟙 X)).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) (𝟙 X)).app M)) this
      ((lowerStarComp.{u + 2, u} (ModuleCat.{u + 1} A)
        (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp (𝟙 X))).app M)
  apply (cancel_mono ((compactificationSheafToDirectImage A
    (Compactification.ofIsProper (𝟙 X))).app M)).1
  erw [graph_open_sheaf_normalization A (𝟙 X) (Compactification.ofIsProper (𝟙 X)) M]
  simp only [NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    compactificationSheafToDirectImage, Compactification.ofIsProper,
    Functor.whiskerRight_app, Category.id_comp]
  erw [lowerStarComp_id_right (ModuleCat.{u + 1} A) (𝟙 X)]
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  erw [Category.comp_id]
  have h := (lowerStarId (ModuleCat.{u + 1} A) X).inv.naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) (𝟙 X)).app M)
  dsimp only [Functor.comp_map, Functor.id_map] at h
  erw [← reassoc_of% h, Iso.inv_hom_id_app, Category.comp_id]

private lemma sheaf_refinement_algebra
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : C ⥤ D) (R : D ⥤ E) (T : C ⥤ E) (e : P ⋙ R ≅ T)
    {V W : C} {J I : D} {S F : E}
    (i : V ⟶ W) (j : J ⟶ I) (q : P.obj W ⟶ I)
    (v : T.obj W ⟶ F) (w : R.obj I ⟶ F)
    (a : S ⟶ R.obj J) (b : J ⟶ P.obj V) (c : S ⟶ T.obj V)
    (hb : b ≫ P.map i ≫ q = j)
    (he : R.map q ≫ w = e.hom.app W ≫ v)
    (ha : a ≫ R.map j ≫ w = c ≫ T.map i ≫ v)
    (hm : Mono (T.map i ≫ v)) :
    a ≫ R.map b ≫ e.hom.app V = c := by
  let := hm
  apply (cancel_mono (T.map i ≫ v)).1
  simp only [Category.assoc]
  erw [← e.hom.naturality_assoc]
  dsimp only [Functor.comp_map]
  erw [← he, ← R.map_comp_assoc, ← R.map_comp_assoc, Category.assoc, hb]
  exact ha

private theorem graph_sheaf_refinement
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    (c d : Compactification f) (r : c.Refinement d)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleCompactificationGraphMap A f d).app M ≫
      (lowerStar (ModuleCat.{u + 1} A) d.g).map
        ((etaleCompactificationGraphMap A d.i (refinementOpenCompactification r)).app M) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) r.hom d.g c.g r.hom_g.symm).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M) =
      (etaleCompactificationGraphMap A f c).app M := by
  have : Mono ((openImmersionLowerShriekToLowerStar
      (ModuleCat.{u + 1} A) c.i).app M) := open_compare_mono.{u} A c.i M
  have hm : Mono ((lowerStar (ModuleCat.{u + 1} A) c.g).map
      ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) c.i c.g f c.comm).hom.app M) := by
    have : Mono ((lowerStar (ModuleCat.{u + 1} A) c.g).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M)) :=
      Functor.map_mono (lowerStar (ModuleCat.{u + 1} A) c.g) _
    exact mono_comp_iso
      ((lowerStar (ModuleCat.{u + 1} A) c.g).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M)) this
      ((lowerStarComp.{u + 2, u} (ModuleCat.{u + 1} A) c.i c.g f c.comm).app M)
  refine sheaf_refinement_algebra
    (C := Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (D := Sheaf d.Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (E := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (lowerStar (ModuleCat.{u + 1} A) r.hom)
    (lowerStar (ModuleCat.{u + 1} A) d.g)
    (lowerStar (ModuleCat.{u + 1} A) c.g)
    (lowerStarComp (ModuleCat.{u + 1} A) r.hom d.g c.g r.hom_g.symm)
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M)
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) d.i).app M)
    ((lowerStarComp (ModuleCat.{u + 1} A) c.i r.hom d.i r.i_hom.symm).hom.app M)
    ((lowerStarComp (ModuleCat.{u + 1} A) c.i c.g f c.comm).hom.app M)
    ((lowerStarComp (ModuleCat.{u + 1} A) d.i d.g f d.comm).hom.app M)
    ((etaleCompactificationGraphMap A f d).app M)
    ((etaleCompactificationGraphMap A d.i (refinementOpenCompactification r)).app M)
    ((etaleCompactificationGraphMap A f c).app M) ?_ ?_ ?_
    hm
  · exact graph_open_sheaf_normalization A d.i (refinementOpenCompactification r) M
  · exact congr_app (lowerStarComp_assoc' (ModuleCat.{u + 1} A)
      c.i r.hom d.g d.i c.g f r.i_hom.symm r.hom_g.symm d.comm) M
  · exact (compactSupportGraphSheafComparison_normalization A f d M).trans
      (compactSupportGraphSheafComparison_normalization A f c M).symm

private lemma exact_identity_fac
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) (K : HomotopyCategory C (.up ℤ)) :
    F.mapDerivedCategoryFactorsh.inv.app K ≫
        (Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Qh.obj K) ≫
        (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) := by
  erw [Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj,
    Functor.mapDerivedCategoryNatIso_fach e K, Iso.inv_hom_id_app_assoc]

private lemma homotopy_identity_composite
    {C : Type*} [Category C] [Abelian C]
    (J R : C ⥤ C) [J.Additive] [R.Additive] (e : R ≅ 𝟭 C)
    (K : HomotopyCategory C (.up ℤ)) :
    (NatTrans.mapHomotopyCategory
      ((Functor.rightUnitor J).inv ≫ Functor.whiskerLeft J e.inv) (.up ℤ)).app K ≫
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
        ((J.mapHomotopyCategory (.up ℤ)).obj K) = 𝟙 _ := by
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ = _
  erw [← (HomotopyCategory.quotient C (.up ℤ)).map_comp,
    ← (HomotopyCategory.quotient C (.up ℤ)).map_id]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    NatTrans.mapHomologicalComplex_app_f, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Category.id_comp]
  exact e.inv_hom_id_app _

private lemma derived_identity_algebra
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions C]
    (J R : C ⥤ C) [J.Additive] [R.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (e : R ≅ 𝟭 C) (K : HomotopyCategory C (.up ℤ)) :
    J.mapDerivedCategoryFactorsh.hom.app K ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory
          ((Functor.rightUnitor J).inv ≫ Functor.whiskerLeft J e.inv) (.up ℤ)).app K) ≫
      R.rightDerivedFunctorUnit.app ((J.mapHomotopyCategory (.up ℤ)).obj K) ≫
      R.rightDerivedFunctor.map (J.mapDerivedCategoryFactorsh.inv.app K) ≫
      R.rightDerivedFunctorIsoMapDerivedCategory.hom.app
        (J.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app
        (J.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
      (Functor.mapDerivedCategoryIdIso C).hom.app
        (J.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) = 𝟙 _ := by
  erw [R.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  have hc := congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((J.mapHomotopyCategory (.up ℤ)).obj K)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hc
  erw [reassoc_of% hc]
  erw [(Functor.mapDerivedCategoryNatIso e).hom.naturality_assoc]
  erw [(Functor.mapDerivedCategoryIdIso C).hom.naturality]
  dsimp only [Functor.comp_map, Functor.id_map]
  erw [reassoc_of% (exact_identity_fac R e
    ((J.mapHomotopyCategory (.up ℤ)).obj K))]
  erw [← DerivedCategory.Qh.map_comp_assoc, homotopy_identity_composite,
    DerivedCategory.Qh.map_id,
    Category.id_comp, Iso.hom_inv_id_app]

private lemma normalizationHomotopyComponent_refinement
    {C D E F : Type v} [Category.{w} C] [Category.{w} D]
    [Category.{w} E] [Category.{w} F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory F]
    [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions E]
    (S : C ⥤ F) (J : C ⥤ D) (I : C ⥤ E)
    (P : D ⥤ E) (R : E ⥤ F) (T : D ⥤ F)
    [S.Additive] [J.Additive] [I.Additive] [P.Additive] [R.Additive] [T.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [P.PreservesKInjectiveComplexes]
    (a : S ⟶ I ⋙ R) (b : I ⟶ J ⋙ P) (c : S ⟶ J ⋙ T)
    (e : P ⋙ R ≅ T)
    (hs : a ≫ Functor.whiskerRight b R ≫ Functor.whiskerLeft J e.hom = c)
    (K : HomotopyCategory C (.up ℤ)) :
    normalizationHomotopyComponent S I R a K ≫
        R.rightDerivedFunctor.map (normalizationHomotopyComponent I J P b K) ≫
        (Functor.rightDerivedFunctorCompIso' P R e).hom.app
          (J.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) =
      normalizationHomotopyComponent S J T c K := by
  unfold normalizationHomotopyComponent
  simp only [homotopy_comp_inv, DerivedCategory.Qh.map_id, Category.id_comp,
    Functor.map_comp, Category.assoc]
  erw [← R.rightDerivedFunctor.map_comp_assoc,
    I.mapDerivedCategoryFactorsh.inv_hom_id_app,
    R.rightDerivedFunctor.map_id, Category.id_comp]
  have hn := R.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory b (.up ℤ)).app K)
  dsimp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  have hn' := (Functor.rightDerivedFunctorCompIso' P R e).hom.naturality
    (J.mapDerivedCategoryFactorsh.inv.app K)
  dsimp only [Functor.comp_map] at hn'
  erw [hn']
  have hc := congr_app (comp_fac P R T e) ((J.mapHomotopyCategory (.up ℤ)).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, comp_unit_app] at hc
  erw [reassoc_of% hc]
  have hh := congr_app
    (congrArg (fun t ↦ NatTrans.mapHomotopyCategory t (.up ℤ)) hs) K
  simp only [NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app] at hh
  change (NatTrans.mapHomotopyCategory a (.up ℤ)).app K ≫
      (R.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory b (.up ℤ)).app K) ≫
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
        ((J.mapHomotopyCategory (.up ℤ)).obj K) =
      (NatTrans.mapHomotopyCategory c (.up ℤ)).app K at hh
  erw [← DerivedCategory.Qh.map_comp_assoc, ← DerivedCategory.Qh.map_comp_assoc, Category.assoc, hh]

attribute [local instance 2000] Abelian.toPreadditive

private lemma compact_support_graph_component
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    (c : Compactification f)
    (K : HomotopyCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    (compactSupportDerivedComparison A f c (etaleCompactificationGraphMap A f c)).app
        (DerivedCategory.Qh.obj K) =
      normalizationHomotopyComponent (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance)
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
        (lowerStar (ModuleCat.{u + 1} A) c.g) (etaleCompactificationGraphMap A f c) K := by
  have h := compactSupportDerivedComparison_app A f c (etaleCompactificationGraphMap A f c) K
  exact h

private theorem graph_identity_derived
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    compactSupportDerivedComparison A (𝟙 X) (Compactification.ofIsProper (𝟙 X))
        (etaleCompactificationGraphMap A (𝟙 X) (Compactification.ofIsProper (𝟙 X))) ≫
      (identityEtaleCompactSupportComparison A X).hom = 𝟙 _ := by
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (.up ℤ))
  intro K
  dsimp only [NatTrans.comp_app, NatTrans.id_app]
  erw [compact_support_graph_component]
  have h := derived_identity_algebra
    (etaleLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) inferInstance)
    (lowerStar (ModuleCat.{u + 1} A) (𝟙 X)) (lowerStarId (ModuleCat.{u + 1} A) X) K
  erw [← graph_identity_sheaf A X] at h
  unfold normalizationHomotopyComponent
  simp only [homotopy_comp_inv, DerivedCategory.Qh.map_id, Category.id_comp]
  dsimp only [identityEtaleCompactSupportComparison,
    Compactification.ofIsProper,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.assoc,
    Category.comp_id]
  erw [Category.assoc, Category.comp_id]
  simp only [Category.assoc]
  congr 1

private theorem graph_derived_refinement
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    (c d : Compactification f) (r : c.Refinement d) :
    compactSupportDerivedComparison A f d (etaleCompactificationGraphMap A f d) ≫
      Functor.whiskerRight (compactSupportDerivedComparison A d.i
        (refinementOpenCompactification r)
        (etaleCompactificationGraphMap A d.i (refinementOpenCompactification r)))
          (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar (ModuleCat.{u + 1} A) r.hom)
          (lowerStar (ModuleCat.{u + 1} A) d.g)
          (lowerStarComp (ModuleCat.{u + 1} A) r.hom d.g c.g r.hom_g.symm)).hom =
      compactSupportDerivedComparison A f c (etaleCompactificationGraphMap A f c) := by
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (.up ℤ))
  intro K
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app]
  erw [Category.id_comp, compact_support_graph_component, compact_support_graph_component,
    compact_support_graph_component]
  have hs : etaleCompactificationGraphMap A f d ≫
      Functor.whiskerRight
        (etaleCompactificationGraphMap A d.i (refinementOpenCompactification r))
        (lowerStar (ModuleCat.{u + 1} A) d.g) ≫
      Functor.whiskerLeft (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
        (lowerStarComp (ModuleCat.{u + 1} A) r.hom d.g c.g r.hom_g.symm).hom =
      etaleCompactificationGraphMap A f c := by
    apply NatTrans.ext
    funext M
    exact graph_sheaf_refinement A f c d r M
  exact normalizationHomotopyComponent_refinement
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance)
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i)
    (lowerStar (ModuleCat.{u + 1} A) r.hom)
    (lowerStar (ModuleCat.{u + 1} A) d.g)
    (lowerStar (ModuleCat.{u + 1} A) c.g)
    (etaleCompactificationGraphMap A f d)
    (etaleCompactificationGraphMap A d.i (refinementOpenCompactification r))
    (etaleCompactificationGraphMap A f c)
    (lowerStarComp (ModuleCat.{u + 1} A) r.hom d.g c.g r.hom_g.symm) hs K

/-- Base change, proper refinement and identity for the specified graph comparison.
Source: SGA 4 XVII 5.2.2, 6.2.11; Stacks Project Tags 03S6, 0F7B and 0F7C.
(blueprint: lem-asd-compact-support-graph-coherence).

Proof:
1. Use the existing forward graph-comparison exchange equation for an arbitrary base
change. Identify its comparison with the specified graph-derived map, and cancel the
invertible graph comparisons to obtain the equation for their inverses.
2. The inclusion from open extension by zero into direct image is monic: its pullback
on the open is invertible, while its pullback on the closed complement has zero
source. The kernel therefore vanishes. Direct image preserves this monomorphism.
For a proper refinement, postcompose the two graph maps with this inclusion. Graph
normalization and associativity of direct-image composition identify the results.
Cancel the monomorphism to obtain the forward sheaf refinement equation.
3. Normalize the derived graph component on a homotopy representative using the exact
source factorization, the sheaf graph map and the right-derived unit. In its composite
cancel the intermediate exact factors, move the unit by naturality, and apply the
existing derived direct-image composition factorization and unit formula. The sheaf
refinement equation then gives derived refinement. Localization extends the equality
to all derived objects; cancel the invertible graph maps for the required orientation.
4. For the proper identity compactification, sheaf normalization, monicity, and the
right unit law for direct image identify the graph map with the inverse direct-image
identity comparison. Its derived unit cancels against the exact-derived comparison.
The exact identity factorization equation and a degreewise homotopy cancellation
identify the remaining map with the identity. Localization and cancellation give
exactly the specified identityEtaleCompactSupportComparison.
These equalities hold on all unbounded complexes, with empty fibres allowed. -/
theorem etaleCompactSupportGraph_coherence
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    EtaleCompactSupportCoherence A (canonicalEtaleCompactSupportCore A) := by
  constructor
  · intro U X X' f hf hs hq hU hcU hX hcX hX' hcX' c g
    ext K
    have h := NatTrans.congr_app
      (GraphExchange.comparison_exact_baseChange A f c g) K
    erw [← GraphExchange.graph_comparison_eq A f c,
      ← GraphExchange.graph_comparison_eq A (pullback.fst g f)
        (c.ofIsPullback (IsPullback.of_hasPullback g f).flip)] at h
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at h ⊢
    change (exactCompactSupportExchange A c g).app K ≫
      (canonicalEtaleCompactSupportComparison A (pullback.fst g f)
        (c.ofIsPullback (IsPullback.of_hasPullback g f).flip)).hom.app _ =
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.map
        ((canonicalEtaleCompactSupportComparison A f c).hom.app K) ≫ _
    apply (cancel_epi ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.map
      ((canonicalEtaleCompactSupportComparison A f c).inv.app K))).1
    dsimp only [canonicalEtaleCompactSupportComparison, Iso.symm_inv, asIso_hom] at h ⊢
    simp only [Iso.symm_hom, asIso_inv]
    erw [← Category.assoc, h]
    simp only [Category.assoc, ← Functor.map_comp_assoc,
      ← NatTrans.comp_app, IsIso.hom_inv_id, NatTrans.id_app]
    erw [(upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.map_id,
      Category.id_comp, Category.comp_id]
  · intro U X f hf hs hU hcU hX hcX c d r hd hdc
    have := isIso_compactSupportGraphDerivedComparison A f c
    have := isIso_compactSupportGraphDerivedComparison A f d
    change Functor.whiskerRight
      (compactSupportDerivedComparison A d.i (refinementOpenCompactification r)
        (etaleCompactificationGraphMap A d.i (refinementOpenCompactification r)))
        (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar (ModuleCat.{u + 1} A) r.hom)
          (lowerStar (ModuleCat.{u + 1} A) d.g)
          (lowerStarComp (ModuleCat.{u + 1} A) r.hom d.g c.g r.hom_g.symm)).hom ≫
      inv (compactSupportDerivedComparison A f c (etaleCompactificationGraphMap A f c)) =
      inv (compactSupportDerivedComparison A f d (etaleCompactificationGraphMap A f d))
    apply (cancel_epi
      (compactSupportDerivedComparison A f d (etaleCompactificationGraphMap A f d))).1
    have h := congrArg
      (fun t ↦ t ≫ inv (compactSupportDerivedComparison A f c
        (etaleCompactificationGraphMap A f c))) (graph_derived_refinement A f c d r)
    erw [IsIso.hom_inv_id] at h
    erw [IsIso.hom_inv_id]
    simpa only [Category.assoc] using h
  · intro X hX hcX
    apply Iso.ext
    apply (cancel_epi ((canonicalEtaleCompactSupportComparison A (𝟙 X)
      (Compactification.ofIsProper (𝟙 X))).inv)).1
    change (canonicalEtaleCompactSupportComparison A (𝟙 X)
      (Compactification.ofIsProper (𝟙 X))).inv ≫
        (canonicalEtaleCompactSupportComparison A (𝟙 X)
          (Compactification.ofIsProper (𝟙 X))).hom = _
    erw [Iso.inv_hom_id]
    exact (graph_identity_derived A X).symm

end AlgebraicGeometry.Etale
