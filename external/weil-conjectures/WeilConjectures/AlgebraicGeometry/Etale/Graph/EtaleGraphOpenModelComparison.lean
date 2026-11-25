/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphCoherence

/-! # The graph comparison in the standard compactification of an open immersion -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Abelian.toPreadditive

attribute [local irreducible] lowerStar upperStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunction mapDerivedUpperStarLowerStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr

-- The graph normalization specializes to the identity proper model of an open immersion.
private theorem graph_open_model_sheaf
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] :
    etaleCompactificationGraphMap A j (Compactification.ofIsOpenImmersion j) =
      (Functor.rightUnitor
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)).inv ≫
      Functor.whiskerLeft (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)
        (lowerStarId (ModuleCat.{u + 1} A) Y).inv := by
  apply NatTrans.ext
  funext M
  have : Mono ((openImmersionLowerShriekToLowerStar
      (ModuleCat.{u + 1} A) j).app M) := open_compare_mono.{u} A j M
  have : Mono ((compactificationSheafToDirectImage A
      (Compactification.ofIsOpenImmersion j)).app M) := by
    dsimp only [compactificationSheafToDirectImage, NatTrans.comp_app,
      Functor.whiskerRight_app]
    have : Mono ((lowerStar (ModuleCat.{u + 1} A) (𝟙 Y)).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j).app M)) :=
      Functor.map_mono (lowerStar (ModuleCat.{u + 1} A) (𝟙 Y)) _
    exact mono_comp_iso _ this
      ((lowerStarComp.{u + 2, u} (ModuleCat.{u + 1} A)
        j (𝟙 Y) j (Category.comp_id j).symm).app M)
  apply (cancel_mono ((compactificationSheafToDirectImage A
    (Compactification.ofIsOpenImmersion j)).app M)).1
  erw [graph_open_sheaf_normalization A j (Compactification.ofIsOpenImmersion j) M]
  simp only [NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    compactificationSheafToDirectImage, Compactification.ofIsOpenImmersion,
    Functor.whiskerRight_app]
  erw [lowerStarComp_id_right (ModuleCat.{u + 1} A) j]
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  erw [Category.comp_id]
  have h := (lowerStarId (ModuleCat.{u + 1} A) Y).inv.naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j).app M)
  dsimp only [Functor.comp_map, Functor.id_map] at h
  erw [← reassoc_of% h, Iso.inv_hom_id_app, Category.comp_id]

private lemma open_homotopy_identity_composite
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (J : C ⥤ D) (R : D ⥤ D) [J.Additive] [R.Additive] (e : R ≅ 𝟭 D)
    (K : HomotopyCategory C (.up ℤ)) :
    (NatTrans.mapHomotopyCategory
      ((Functor.rightUnitor J).inv ≫ Functor.whiskerLeft J e.inv) (.up ℤ)).app K ≫
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app
        ((J.mapHomotopyCategory (.up ℤ)).obj K) = 𝟙 _ := by
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change (HomotopyCategory.quotient D (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient D (.up ℤ)).map _ = _
  erw [← (HomotopyCategory.quotient D (.up ℤ)).map_comp,
    ← (HomotopyCategory.quotient D (.up ℤ)).map_id]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    NatTrans.mapHomologicalComplex_app_f, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Category.id_comp]
  exact e.inv_hom_id_app _

private lemma open_derived_identity_algebra
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions D]
    (J : C ⥤ D) (R : D ⥤ D) [J.Additive] [R.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (e : R ≅ 𝟭 D) (K : HomotopyCategory C (.up ℤ)) :
    normalizationHomotopyComponent J J R
        ((Functor.rightUnitor J).inv ≫ Functor.whiskerLeft J e.inv) K ≫
      R.rightDerivedFunctorIsoMapDerivedCategory.hom.app
        (J.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app
        (J.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) ≫
      (Functor.mapDerivedCategoryIdIso D).hom.app
        (J.mapDerivedCategory.obj (DerivedCategory.Qh.obj K)) = 𝟙 _ := by
  unfold normalizationHomotopyComponent
  simp only [homotopy_comp_inv, DerivedCategory.Qh.map_id, Category.id_comp,
    Category.assoc]
  erw [R.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  have hc := congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((J.mapHomotopyCategory (.up ℤ)).obj K)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hc
  erw [reassoc_of% hc]
  erw [(Functor.mapDerivedCategoryNatIso e).hom.naturality_assoc]
  erw [(Functor.mapDerivedCategoryIdIso D).hom.naturality]
  dsimp only [Functor.comp_map, Functor.id_map]
  erw [reassoc_of% (exact_identity_fac R e
    ((J.mapHomotopyCategory (.up ℤ)).obj K))]
  erw [← DerivedCategory.Qh.map_comp_assoc, open_homotopy_identity_composite,
    DerivedCategory.Qh.map_id,
    Category.id_comp, Iso.hom_inv_id_app]
  rfl

/-- The graph comparison for an open immersion in its identity-proper compactification
is precisely removal of the identity direct image.
Source: Stacks Project, etale-cohomology.tex Tag 0F4L; SGA 4 XVII 6.2.11.
(blueprint: lem-pur-etale-graph-open-model-comparison).

Proof: postcompose the sheaf graph map with the monic compactification inclusion in
ordinary direct image. Graph normalization identifies that composite with the usual
open-extension inclusion. The right identity law and naturality for direct image give
the same composite for the inverse identity comparison, so monicity identifies the
sheaf maps. Evaluate the derived comparison on a homotopy representative. Move its
exact factorization through the right-derived identity comparison by naturality; its
right-derived unit cancels against the exact identity factorization. The degreewise
sheaf identity then cancels the remaining factors. Localization extends this equation
to every derived object, and cancellation of the invertible graph map gives the stated
inverse comparison. The argument includes the identity and empty open immersions. -/
theorem etaleGraphOpenModelComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j] :
    canonicalEtaleCompactSupportComparison A j (Compactification.ofIsOpenImmersion j) =
      Functor.isoWhiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
        (rightDerivedLowerStarIdIso A Y) ≪≫ Functor.rightUnitor _ := by
  apply Iso.ext
  apply (cancel_epi (canonicalEtaleCompactSupportComparison A j
    (Compactification.ofIsOpenImmersion j)).inv).1
  rw [Iso.inv_hom_id]
  symm
  unfold canonicalEtaleCompactSupportComparison
  change compactSupportDerivedComparison A j (Compactification.ofIsOpenImmersion j)
    (etaleCompactificationGraphMap A j (Compactification.ofIsOpenImmersion j)) ≫ _ = 𝟙 _
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (.up ℤ))
  intro K
  dsimp only [NatTrans.comp_app, NatTrans.id_app]
  erw [compact_support_graph_component]
  have h := open_derived_identity_algebra
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j)
    (lowerStar (ModuleCat.{u + 1} A) (𝟙 Y)) (lowerStarId (ModuleCat.{u + 1} A) Y) K
  erw [← graph_open_model_sheaf A j] at h
  dsimp only [Compactification.ofIsOpenImmersion, rightDerivedLowerStarIdIso,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.assoc,
    Category.comp_id]
  erw [Category.comp_id]
  exact h

end AlgebraicGeometry.Etale
