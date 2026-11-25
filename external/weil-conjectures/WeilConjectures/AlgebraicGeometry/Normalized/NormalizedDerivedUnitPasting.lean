/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Pasting normalized derived units

## References

* Stacks Project, Tags 0F7B, 0F7J and 0D6E
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private lemma comp_homotopy_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (K : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K = 𝟙 _ := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change (HomotopyCategory.quotient E (.up ℤ)).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

private lemma right_comp_unit_raw
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (R : C ⥤ D) (P : D ⥤ E) [R.Additive] [P.Additive]
    [R.PreservesKInjectiveComplexes] {S : C ⥤ E} [S.Additive]
    (e : R ⋙ P ≅ S) (K : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit R P).app K ≫
        (Functor.rightDerivedFunctorCompIso' R P e).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((e.hom.mapHomotopyCategory (.up ℤ)).app K) ≫
        S.rightDerivedFunctorUnit.app K := by
  have h : (Functor.rightDerivedFunctorCompUnit R P).app K ≫
      (Functor.rightDerivedFunctorCompIso' R P e).hom.app (DerivedCategory.Qh.obj K) =
      (R ⋙ P).rightDerivedFunctorUnit.app K ≫
        (Functor.rightDerivedFunctorNatTrans e.hom).app (DerivedCategory.Qh.obj K) := by
    simp [Functor.rightDerivedFunctorCompIso', Functor.rightDerivedFunctorCompIso,
      Functor.rightDerivedFunctorNatIso]
  rw [h]
  exact Functor.rightDerivedNatTrans_app (R ⋙ P).rightDerivedFunctor S.rightDerivedFunctor
    (R ⋙ P).rightDerivedFunctorUnit S.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
    (Functor.whiskerRight (e.hom.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh) K

private lemma right_comp_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (R : C ⥤ D) (P : D ⥤ E) [R.Additive] [P.Additive]
    [R.PreservesKInjectiveComplexes] {S : C ⥤ E} [S.Additive]
    (e : R ⋙ P ≅ S) (K : HomotopyCategory C (.up ℤ)) :
    P.rightDerivedFunctorUnit.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
        P.rightDerivedFunctor.map (R.rightDerivedFunctorUnit.app K) ≫
        (Functor.rightDerivedFunctorCompIso' R P e).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ P)) (.up ℤ)).hom.app K ≫
          (e.hom.mapHomotopyCategory (.up ℤ)).app K) ≫
        S.rightDerivedFunctorUnit.app K := by
  have h := right_comp_unit_raw R P e K
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc] at h
  apply (cancel_epi (DerivedCategory.Qh.map
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ P)) (.up ℤ)).inv.app K))).1
  simp only [← DerivedCategory.Qh.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  exact h

section Pasting
private noncomputable abbrev nunit
    {C₀ D₀ E₀ : Type*} [Category C₀] [Category D₀] [Category E₀]
    [Abelian C₀] [Abelian D₀] [Abelian E₀]
    [HasDerivedCategory C₀] [HasDerivedCategory D₀] [HasDerivedCategory E₀]
    [Abelian.HasKInjectiveResolutions D₀]
    (F₀ : C₀ ⥤ E₀) (J₀ : C₀ ⥤ D₀) (R₀ : D₀ ⥤ E₀)
    [F₀.Additive] [J₀.Additive] [R₀.Additive]
    [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    [PreservesFiniteLimits J₀] [PreservesFiniteColimits J₀]
    (a₀ : F₀ ⟶ J₀ ⋙ R₀) :=
  normalizationLocalizationDesc DerivedCategory.Qh (HomotopyCategory.quasiIso C₀ (.up ℤ))
    (normalizationHomotopyTransformation F₀ J₀ R₀ a₀)

private lemma nunit_app
    {C₀ D₀ E₀ : Type*} [Category C₀] [Category D₀] [Category E₀]
    [Abelian C₀] [Abelian D₀] [Abelian E₀]
    [HasDerivedCategory C₀] [HasDerivedCategory D₀] [HasDerivedCategory E₀]
    [Abelian.HasKInjectiveResolutions D₀]
    (F₀ : C₀ ⥤ E₀) (J₀ : C₀ ⥤ D₀) (R₀ : D₀ ⥤ E₀)
    [F₀.Additive] [J₀.Additive] [R₀.Additive]
    [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    [PreservesFiniteLimits J₀] [PreservesFiniteColimits J₀]
    (a₀ : F₀ ⟶ J₀ ⋙ R₀) (K : HomotopyCategory C₀ (.up ℤ)) :
    (nunit F₀ J₀ R₀ a₀).app (DerivedCategory.Qh.obj K) =
      normalizationHomotopyComponent F₀ J₀ R₀ a₀ K := by
  rw [nunit, normalizationLocalizationDesc_app, normalizationHomotopyTransformation_app]

/-- Normalized exact/right-derived units paste across a mixed exchange satisfying its
unit identity. Precompose by the fully faithful homotopy localization, expand the two
normalized units, and move the input maps through the factors by naturality. Apply the
mixed unit identity and the right-derived composition unit formula. Cancel the exact
open-composition factors. The remaining homotopy identity is checked on complexes,
degree by degree, using naturality of the second ordinary input map. -/
theorem normalizedDerivedUnitPasting
    {C U Y X Z B : Type*}
  [Category C] [Category U] [Category Y] [Category X] [Category Z] [Category B]
  [Abelian C] [Abelian U] [Abelian Y] [Abelian X] [Abelian Z] [Abelian B]
  [HasDerivedCategory C] [HasDerivedCategory U] [HasDerivedCategory Y]
  [HasDerivedCategory X] [HasDerivedCategory Z] [HasDerivedCategory B]
  [Abelian.HasKInjectiveResolutions U] [Abelian.HasKInjectiveResolutions X]
  [Abelian.HasKInjectiveResolutions Z]
  (J : C ⥤ U) (R : U ⥤ Y) (I : Y ⥤ Z) (O : U ⥤ X)
  (P : X ⥤ Z) (S : Z ⥤ B) (H : C ⥤ X) (W : X ⥤ B)
  (F : C ⥤ Y) (G : Y ⥤ B)
  [J.Additive] [R.Additive] [I.Additive] [O.Additive] [P.Additive] [S.Additive]
  [H.Additive] [W.Additive] [F.Additive] [G.Additive]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  [PreservesFiniteLimits O] [PreservesFiniteColimits O]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [P.PreservesKInjectiveComplexes]
    (ah : F ⟶ J ⋙ R) (ae : G ⟶ I ⋙ S)
    (χ : R ⋙ I ⟶ O ⋙ P)
    (Γ : R.rightDerivedFunctor ⋙ I.mapDerivedCategory ⟶
      O.mapDerivedCategory ⋙ P.rightDerivedFunctor)
    (hn : ∀ K : HomotopyCategory U (.up ℤ),
      I.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
          Γ.app (DerivedCategory.Qh.obj K) ≫
          P.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.hom.app K) =
        I.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ I)) (.up ℤ)).hom.app K ≫
              (χ.mapHomotopyCategory (.up ℤ)).app K ≫
              (Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ P)) (.up ℤ)).inv.app K) ≫
          P.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj K))
    (eo : H ≅ J ⋙ O) (ep : P ⋙ S ≅ W) :
    Functor.whiskerRight (normalizationLocalizationDesc DerivedCategory.Qh
          (HomotopyCategory.quasiIso C (.up ℤ))
          (normalizationHomotopyTransformation F J R ah)) G.mapDerivedCategory ≫
        Functor.whiskerLeft (J.mapDerivedCategory ⋙ R.rightDerivedFunctor)
          (normalizationLocalizationDesc DerivedCategory.Qh
          (HomotopyCategory.quasiIso Y (.up ℤ))
          (normalizationHomotopyTransformation G I S ae)) ≫
        Functor.whiskerLeft J.mapDerivedCategory (Functor.whiskerRight Γ S.rightDerivedFunctor) ≫
        Functor.whiskerLeft (J.mapDerivedCategory ⋙ O.mapDerivedCategory)
          (Functor.rightDerivedFunctorCompIso' P S ep).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryTriangleIso eo).inv
          W.rightDerivedFunctor =
      (Functor.mapDerivedCategoryCompIso F G).hom ≫
        (fun a₀ ↦ normalizationLocalizationDesc DerivedCategory.Qh
          (HomotopyCategory.quasiIso C (.up ℤ))
          (normalizationHomotopyTransformation (F ⋙ G) H W a₀))
          (Functor.whiskerRight ah G ≫ Functor.whiskerLeft J (Functor.whiskerLeft R ae) ≫
            Functor.whiskerLeft J (Functor.whiskerRight χ S) ≫
            Functor.whiskerLeft (J ⋙ O) ep.hom ≫ Functor.whiskerRight eo.inv W) := by
  apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ)) _).map_injective
  change Functor.whiskerLeft DerivedCategory.Qh
    (Functor.whiskerRight (nunit F J R ah) G.mapDerivedCategory ≫
      Functor.whiskerLeft (J.mapDerivedCategory ⋙ R.rightDerivedFunctor) (nunit G I S ae) ≫
      Functor.whiskerLeft J.mapDerivedCategory (Functor.whiskerRight Γ S.rightDerivedFunctor) ≫
      Functor.whiskerLeft (J.mapDerivedCategory ⋙ O.mapDerivedCategory)
        (Functor.rightDerivedFunctorCompIso' P S ep).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategoryTriangleIso eo).inv
        W.rightDerivedFunctor) = Functor.whiskerLeft DerivedCategory.Qh
      ((Functor.mapDerivedCategoryCompIso F G).hom ≫
        nunit (F ⋙ G) H W
          (Functor.whiskerRight ah G ≫ Functor.whiskerLeft J (Functor.whiskerLeft R ae) ≫
            Functor.whiskerLeft J (Functor.whiskerRight χ S) ≫
            Functor.whiskerLeft (J ⋙ O) ep.hom ≫ Functor.whiskerRight eo.inv W))
  ext K
  let α := (ah.mapHomotopyCategory (.up ℤ)).app K ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (J ⋙ R)) (.up ℤ)).inv.app K
  let γ := (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ I)) (.up ℤ)).hom.app
      ((J.mapHomotopyCategory (.up ℤ)).obj K) ≫
    (χ.mapHomotopyCategory (.up ℤ)).app ((J.mapHomotopyCategory (.up ℤ)).obj K) ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ P)) (.up ℤ)).inv.app
      ((J.mapHomotopyCategory (.up ℤ)).obj K)
  let κ := (Functor.mapHomotopyCategoryCompIso (Iso.refl (P ⋙ S)) (.up ℤ)).hom.app
      ((O.mapHomotopyCategory (.up ℤ)).obj ((J.mapHomotopyCategory (.up ℤ)).obj K)) ≫
    (ep.hom.mapHomotopyCategory (.up ℤ)).app
      ((O.mapHomotopyCategory (.up ℤ)).obj ((J.mapHomotopyCategory (.up ℤ)).obj K))
  let w := (eo.hom.mapHomotopyCategory (.up ℤ)).app K ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (J ⋙ O)) (.up ℤ)).inv.app K
  let ta := Functor.whiskerRight ah G ≫ Functor.whiskerLeft J (Functor.whiskerLeft R ae) ≫
    Functor.whiskerLeft J (Functor.whiskerRight χ S) ≫
    Functor.whiskerLeft (J ⋙ O) ep.hom ≫ Functor.whiskerRight eo.inv W
  have ht : (ta.mapHomotopyCategory (.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ W)) (.up ℤ)).inv.app K ≫
      (W.mapHomotopyCategory (.up ℤ)).map w =
      (ae.mapHomotopyCategory (.up ℤ)).app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (I ⋙ S)) (.up ℤ)).inv.app
          ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        (S.mapHomotopyCategory (.up ℤ)).map
          ((I.mapHomotopyCategory (.up ℤ)).map α ≫ γ) ≫ κ := by
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    have hz : (ta.mapHomologicalComplex (.up ℤ)).app L ≫
        (W.mapHomologicalComplex (.up ℤ)).map
          ((eo.hom.mapHomologicalComplex (.up ℤ)).app L) =
        (ae.mapHomologicalComplex (.up ℤ)).app ((F.mapHomologicalComplex (.up ℤ)).obj L) ≫
          (S.mapHomologicalComplex (.up ℤ)).map
            ((I.mapHomologicalComplex (.up ℤ)).map
                ((ah.mapHomologicalComplex (.up ℤ)).app L) ≫
              (χ.mapHomologicalComplex (.up ℤ)).app
                ((J.mapHomologicalComplex (.up ℤ)).obj L)) ≫
          (ep.hom.mapHomologicalComplex (.up ℤ)).app
            ((O.mapHomologicalComplex (.up ℤ)).obj
              ((J.mapHomologicalComplex (.up ℤ)).obj L)) := by
      ext n
      simp only [ta, NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplex_map_f, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
        Category.assoc]
      rw [← W.map_comp, eo.inv_hom_id_app]
      erw [W.map_id, Category.comp_id]
      have hna := ae.naturality (ah.app (L.X n))
      dsimp only [Functor.comp_map, Functor.comp_obj] at hna
      rw [reassoc_of% hna]
      simp only [Functor.map_comp, Category.assoc]
      rfl
    have hh := (HomotopyCategory.quotient B (.up ℤ)).congr_map hz
    simp only [Functor.map_comp] at hh
    simp only [α, γ, κ, w, comp_homotopy_inv,
      Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp,
      Category.comp_id, Functor.map_comp]
    convert hh using 1 <;> rfl
  try simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app]
  rw [nunit_app F J R ah K]
  let v := DerivedCategory.Qh.map ((ah.mapHomotopyCategory (.up ℤ)).app K) ≫
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (J ⋙ R)) (.up ℤ)).inv.app K) ≫
    R.rightDerivedFunctorUnit.app ((J.mapHomotopyCategory (.up ℤ)).obj K) ≫
    R.rightDerivedFunctor.map (J.mapDerivedCategoryFactorsh.inv.app K)
  change G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K ≫ v) ≫ _ = _
  have hv := (nunit G I S ae).naturality v
  dsimp only [Functor.comp_map, Functor.comp_obj] at hv
  rw [G.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  dsimp only [Functor.comp_obj]
  erw [reassoc_of% hv, nunit_app G I S ae]
  rw [nunit_app (F ⋙ G) H W]
  simp only [normalizationHomotopyComponent, v, Functor.map_comp, Category.assoc]
  let da := Functor.mapDerivedCategoryTriangleIso eo
  let z := O.mapDerivedCategory.map (J.mapDerivedCategoryFactorsh.hom.app K) ≫
    O.mapDerivedCategoryFactorsh.hom.app ((J.mapHomotopyCategory (.up ℤ)).obj K)
  apply (cancel_mono (W.rightDerivedFunctor.map
    (da.hom.app (DerivedCategory.Qh.obj K) ≫ z))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [← W.rightDerivedFunctor.map_comp_assoc]
  erw [Iso.inv_hom_id_app, W.rightDerivedFunctor.map_id, Category.id_comp]
  have hc := (Functor.rightDerivedFunctorCompIso' P S ep).hom.naturality z
  dsimp only [Functor.comp_map, Functor.comp_obj] at hc
  rw [← hc]
  simp only [z, Functor.map_comp, Category.assoc]
  have hg := Γ.naturality (J.mapDerivedCategoryFactorsh.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hg
  simp only [← S.rightDerivedFunctor.map_comp_assoc]
  rw [← reassoc_of% hg]
  simp only [← I.mapDerivedCategory.map_comp_assoc,
    ← R.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app]
  erw [R.rightDerivedFunctor.map_id]
  simp only [I.mapDerivedCategory.map_comp, Category.assoc]
  have hi := I.mapDerivedCategoryFactorsh.inv.naturality
    ((ah.mapHomotopyCategory (.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (J ⋙ R)) (.up ℤ)).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hi
  simp only [Functor.map_comp] at hi
  rw [← reassoc_of% hi]
  erw [I.mapDerivedCategory.map_id, Category.id_comp]
  erw [hn ((J.mapHomotopyCategory (.up ℤ)).obj K)]
  rw [Iso.inv_hom_id_app_assoc]
  simp only [← DerivedCategory.Qh.map_comp_assoc,
    ← (I.mapHomotopyCategory (.up ℤ)).map_comp_assoc]
  rw [S.rightDerivedFunctor.map_comp]
  simp only [Category.assoc]
  have hs := S.rightDerivedFunctorUnit.naturality
    ((I.mapHomotopyCategory (.up ℤ)).map α ≫ γ)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hs
  erw [← reassoc_of% hs,
    right_comp_unit P S ep
      ((O.mapHomotopyCategory (.up ℤ)).obj ((J.mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [← W.rightDerivedFunctor.map_comp]
  erw [Functor.mapDerivedCategoryTriangleIso_hom_app_Qh_obj eo K]
  have hw := W.rightDerivedFunctorUnit.naturality w
  dsimp only [Functor.comp_map, Functor.comp_obj] at hw
  rw [← hw]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factorsh F G K]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← DerivedCategory.Qh.map_comp_assoc]
  rw [ht]
end Pasting

end AlgebraicGeometry.Etale
