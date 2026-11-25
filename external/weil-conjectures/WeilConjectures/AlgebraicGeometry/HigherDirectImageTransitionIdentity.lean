/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions


public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Identity
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import all WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyPullbackLaws

/-! # Identity triangle for higher direct images

Source: Stacks Project, Tag 09Z1, canonical comparison maps, and Tag 03Q8.
(blueprint: lem-sbc-higher-image-transition-identity).
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private theorem single_iso_id
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : C ⥤ C) [P.Additive] [Limits.PreservesFiniteLimits P]
    [Limits.PreservesFiniteColimits P] (e : P ≅ 𝟭 C) (X : C) :
    (P.mapDerivedCategoryPlusSingleFunctor 0).hom.app X ≫
      (DerivedCategory.Plus.singleFunctor C 0).map (e.hom.app X) =
    (Functor.mapDerivedCategoryPlusNatIso e ≪≫
      Functor.mapDerivedCategoryPlusIdIso C).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X) := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, Iso.trans_hom, NatTrans.comp_app,
    Functor.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusIdIso_hom_app]
  change (P.mapDerivedCategorySingleFunctor 0).hom.app X ≫
    (DerivedCategory.singleFunctor C 0).map (e.hom.app X) = _
  change _ = (Functor.mapDerivedCategoryNatIso e).hom.app
    (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X)) ≫
      (Functor.mapDerivedCategoryIdIso C).hom.app
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X))
  rw [idFactors, Functor.mapDerivedCategoryNatIso_fac_assoc]
  simp only [Functor.mapDerivedCategorySingleFunctor, Iso.trans_hom, Iso.symm_hom,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    DerivedCategory.singleFunctorIsoCompQ, Category.id_comp]
  erw [P.mapDerivedCategory.map_id, Category.id_comp, Category.comp_id]
  simp only [Category.assoc]
  change P.mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex P
        (ComplexShape.up ℤ) 0).hom.app X) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map (e.hom.app X)) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 2
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst i
    simp only [CochainComplex.singleFunctor, Functor.comp_obj,
      Functor.id_obj, HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl,
      Iso.refl_hom, CategoryTheory.Functor.map_id, Iso.refl_inv, Category.id_comp,
      HomologicalComplex.single_map_f_self, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplexIdIso_hom_app_f]
    change (𝟙 (P.obj X)) ≫ e.hom.app X ≫ 𝟙 X = e.hom.app X ≫ 𝟙 X
    simp only [Category.id_comp]
  · apply (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) 0 X i hi).eq_of_tgt

set_option backward.isDefEq.respectTransparency false in
private theorem transition_id
    (Λ : Type (u + 1)) [CommRing Λ] {S Y : Scheme.{u}} (h : Y ⟶ S)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    lowerStarPlusTransition Λ (𝟙 Y) h h (Category.id_comp h) K ≫
      R+((h)_*[ModuleCat.{u + 1} Λ]).map
        ((upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) Y).hom.app K) = 𝟙 _ := by
  unfold lowerStarPlusTransition
  rw [← upperStarCompDerivedPlus_eq_eqToIso_trans
    (ModuleCat.{u + 1} Λ) (𝟙 Y) h h (Category.id_comp h).symm]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp]
  rw [(upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) Y).hom.naturality]
  simp only [Functor.id_map, Functor.map_comp]
  have hc := NatTrans.congr_app
    (upperStarCompDerivedPlus_id_left (ModuleCat.{u + 1} Λ) h)
    (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app] at hc
  rw [← Functor.map_comp_assoc, hc]
  erw [(R+((h)_*[ModuleCat.{u + 1} Λ])).map_id, Category.id_comp]
  exact Adjunction.right_triangle_components
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h) K

set_option backward.isDefEq.respectTransparency false in
/-- The transition for the identity triangle becomes the identity after identifying
identity pullback with the original sheaf.
Source: Stacks Project, Tag 09Z1, canonical comparisons; Tag 03Q8.
(blueprint: lem-sbc-higher-image-transition-identity).

Proof: Expand the transition before taking homology. The inverse-image composition
comparison for `id ≫ h = h` is the inverse of the identity comparison whiskered by
`h^*`. Move this comparison past the counit by naturality, and cancel the unit and
counit of `h^* ⊣ Rh_*` by the triangle identity. The comparison between derived
identity pullback and identity, followed by the single-functor comparison and the
single-functor image of the sheaf identity comparison, is the identity. This follows
by applying the defining factorization of the exact derived functor to the complex
concentrated in degree zero. Thus the entire derived morphism is the identity.
Apply degree-q homology, which preserves identities. -/
theorem higher_direct_image_transition_identity
    (Λ : Type (u + 1)) [CommRing Λ] {S Y : Scheme.{u}} (h : Y ⟶ S)
    (q : ℤ) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    higherDirectImageTransition Λ (𝟙 Y) h h (Category.id_comp h) q F ≫
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h)_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarId (ModuleCat.{u + 1} Λ) Y).hom.app F))) = 𝟙 _ := by
  have hs' : (((𝟙 Y)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarId (ModuleCat.{u + 1} Λ) Y).hom.app F) =
      (upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) Y).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) :=
    single_iso_id ((𝟙 Y)^*[ModuleCat.{u + 1} Λ])
      (upperStarId (ModuleCat.{u + 1} Λ) Y) F
  let K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let t := lowerStarPlusTransition Λ (𝟙 Y) h h (Category.id_comp h) K
  let s := (((𝟙 Y)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F
  let e := (DerivedCategory.Plus.singleFunctor _ 0).map
    ((upperStarId (ModuleCat.{u + 1} Λ) Y).hom.app F)
  let R := R+((h)_*[ModuleCat.{u + 1} Λ])
  let H := DerivedCategory.Plus.homologyFunctor
    (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q
  change H.map (t ≫ R.map s) ≫ H.map (R.map e) = 𝟙 _
  calc
    _ = H.map ((t ≫ R.map s) ≫ R.map e) := (H.map_comp _ _).symm
    _ = H.map (t ≫ R.map (s ≫ e)) := congrArg H.map
      ((Category.assoc _ _ _).trans
        (congrArg (fun b ↦ t ≫ b) (R.map_comp s e).symm))
    _ = H.map (𝟙 _) := congrArg H.map
      ((congrArg (fun b ↦ t ≫ R.map b) hs').trans (transition_id Λ h K))
    _ = _ := H.map_id _

end AlgebraicGeometry.Etale
