/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Derived adjunctions identified with the identity adjunction

Let `adj : F ⊣ G` be an adjunction of exact endofunctors of an abelian category `C`, together with
isomorphisms `ι : F ≅ 𝟭` and `u : G ≅ 𝟭` identifying it with the identity adjunction, in the
sense that `ι⁻¹ ≫ ε = u` on `G`. Then the levelwise derived adjunction `D(F) ⊣ D(G)` is
identified with the identity adjunction by the derived isomorphisms `D(F) ≅ D(𝟭) ≅ 𝟭` and
`D(G) ≅ D(𝟭) ≅ 𝟭` (`CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_counit_app_of_iso`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Abelian

namespace CategoryTheory.Adjunction

section Uniq

variable {C : Type*} [Category C]

/-- For an adjunction `F ⊣ G` and `u : G ≅ 𝟭`, the identification `F ≅ 𝟭` of the left adjoints of
`𝟭` (`Adjunction.leftAdjointUniq`) is compatible with the counit: `ι⁻¹ ≫ ε = u` on `G`. -/
lemma leftAdjointUniq_ofNatIsoRight_inv_app_comp_counit {F G : C ⥤ C} (adj : F ⊣ G)
    (u : G ≅ 𝟭 C) (Y : C) :
    ((adj.ofNatIsoRight u).leftAdjointUniq Adjunction.id).inv.app (G.obj Y) ≫
      adj.counit.app Y = u.hom.app Y := by
  have h₁ : ((adj.ofNatIsoRight u).leftAdjointUniq Adjunction.id).hom.app Y =
      F.map (u.inv.app Y) ≫ adj.counit.app Y := by
    simpa [Adjunction.ofNatIsoRight_counit] using
      leftAdjointUniq_hom_app_counit (adj.ofNatIsoRight u) Adjunction.id Y
  have h₂ := ((adj.ofNatIsoRight u).leftAdjointUniq Adjunction.id).hom.naturality (u.hom.app Y)
  simp only [Functor.id_map, Functor.id_obj] at h₂
  rw [← cancel_epi (((adj.ofNatIsoRight u).leftAdjointUniq Adjunction.id).hom.app (G.obj Y)),
    Iso.hom_inv_id_app_assoc, ← h₂, h₁, ← F.map_comp_assoc, Iso.hom_inv_id_app, F.map_id,
    Category.id_comp]

end Uniq

section Id

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] {F : C ⥤ C} [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- On the image of an object of the homotopy category, the identification `D(F) ≅ D(𝟭) ≅ 𝟭`
induced by `ι : F ≅ 𝟭` is the image of `ι`. -/
@[reassoc]
lemma mapDerivedCategoryNatIso_trans_idIso_inv_app_Qh_obj (ι : F ≅ 𝟭 C)
    (Z : HomotopyCategory C (.up ℤ)) :
    (Functor.mapDerivedCategoryNatIso ι ≪≫ Functor.mapDerivedCategoryIdIso C).inv.app
        (DerivedCategory.Qh.obj Z) ≫ F.mapDerivedCategoryFactorsh.hom.app Z =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory ι.inv (.up ℤ)).app Z) := by
  have hId : (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Qh.obj Z) =
      (𝟭 C).mapDerivedCategoryFactorsh.hom.app Z := by
    have h := NatTrans.congr_app
      (congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh C)) Z
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h
    have hq : DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app Z) =
        𝟙 (((𝟭 C).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj Z) := by
      rw [Functor.mapHomotopyCategoryIdIso_hom_app_eq_id]
      exact DerivedCategory.Qh.map_id _
    refine (Category.comp_id _).symm.trans (h.trans ?_)
    rw [hq]
    erw [Category.id_comp, Category.comp_id]
  have hι := Functor.mapDerivedCategoryNatIso_fach ι.symm Z
  rw [Functor.mapDerivedCategoryNatIso_symm] at hι
  rw [Iso.trans_inv, NatTrans.comp_app, Category.assoc, hι, ← Category.assoc]
  erw [← hId, Iso.inv_hom_id_app, Category.id_comp]
  rfl

end Id

variable {C : Type*} [Category C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasKInjectiveResolutions C]
  {F G : C ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- An adjunction `F ⊣ G` of exact endofunctors identified with the identity adjunction by
`ι : F ≅ 𝟭` and `u : G ≅ 𝟭` (`ι⁻¹ ≫ ε = u` on `G`) induces a derived adjunction
`D(F) ⊣ D(G)` identified with the identity adjunction by `D(F) ≅ D(𝟭) ≅ 𝟭` and
`D(G) ≅ D(𝟭) ≅ 𝟭`. -/
lemma mapDerivedCategoryAdjunction_counit_app_of_iso (ι : F ≅ 𝟭 C) (u : G ≅ 𝟭 C)
    (h : ∀ Y, ι.inv.app (G.obj Y) ≫ adj.counit.app Y = u.hom.app Y) (Y : DerivedCategory C) :
    (Functor.mapDerivedCategoryNatIso ι ≪≫ Functor.mapDerivedCategoryIdIso C).inv.app
        (G.mapDerivedCategory.obj Y) ≫ adj.mapDerivedCategoryAdjunction.counit.app Y =
      (Functor.mapDerivedCategoryNatIso u ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app Y := by
  have hh (P : HomotopyCategory C (.up ℤ)) :
      (NatTrans.mapHomotopyCategory ι.inv (.up ℤ)).app ((G.mapHomotopyCategory (.up ℤ)).obj P) ≫
        (adj.mapHomotopyCategory (.up ℤ)).counit.app P =
      (NatTrans.mapHomotopyCategory u.hom (.up ℤ)).app P := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    rw [mapHomotopyCategory_counit_app_quotient]
    erw [← (HomotopyCategory.quotient C (.up ℤ)).map_comp]
    congr 1
    ext n
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Adjunction.mapHomologicalComplex_counit_app_f]
    exact h (K.X n)
  have key := Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ))
    (τ := Functor.whiskerLeft G.mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso ι ≪≫ Functor.mapDerivedCategoryIdIso C).inv ≫
      adj.mapDerivedCategoryAdjunction.counit)
    (τ' := (Functor.mapDerivedCategoryNatIso u ≪≫ Functor.mapDerivedCategoryIdIso C).hom)
    (fun P ↦ by
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
      rw [mapDerivedCategoryAdjunction_counit_app_Qh_obj, ← NatTrans.naturality_assoc]
      simp only [Functor.comp_obj, Functor.id_map]
      rw [mapDerivedCategoryNatIso_trans_idIso_inv_app_Qh_obj_assoc, ← Functor.map_comp, hh,
        ← cancel_epi ((Functor.mapDerivedCategoryNatIso u ≪≫
          Functor.mapDerivedCategoryIdIso C).inv.app (DerivedCategory.Qh.obj P)),
        Iso.inv_hom_id_app, reassoc_of% (mapDerivedCategoryNatIso_trans_idIso_inv_app_Qh_obj u P),
        ← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp,
        u.inv_hom_id, NatTrans.mapHomotopyCategory_id]
      simp
      rfl)
  exact NatTrans.congr_app key Y

end CategoryTheory.Adjunction
