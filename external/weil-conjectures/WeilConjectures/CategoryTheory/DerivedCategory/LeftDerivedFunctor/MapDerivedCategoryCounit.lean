/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-!
# Counits of the isomorphisms between left derived functors of exact functors

For exact functors `F`, `G` between abelian categories, the isomorphisms
`Functor.leftDerivedFunctorNatIso`, `Functor.leftDerivedFunctorCompIso` and the identification
`L(𝟭) ≅ 𝟭` are compatible with the counits `Qh ⋙ LF ⟶ F.mapHomotopyCategory ⋙ Qh` of the left
derived functors: on the image of an object of the homotopy category they are induced by the
corresponding isomorphisms of functors on the homotopy categories.

## Main results

- `CategoryTheory.Functor.leftDerivedFunctorNatIso_hom_app_Qh`
- `Functor.leftDerivedFunctorIsoMapDerivedCategory_trans_mapDerivedCategoryIdIso_hom_app_Qh`
- `CategoryTheory.Functor.leftDerivedFunctorCompIso_hom_app_Qh`
- `CategoryTheory.Functor.leftDerivedFunctorCompIso_symm_trans_natIso_hom_app_Qh`
-/

@[expose] public section

universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open MonoidalCategory

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- `Functor.leftDerivedFunctorIsoMapDerivedCategory` followed by the factorization of
`F.mapDerivedCategory` through `DerivedCategory.Qh` is the counit of the left derived functor. -/
@[reassoc]
lemma leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj K) ≫
      F.mapDerivedCategoryFactorsh.hom.app K = F.leftDerivedFunctorCounit.app K :=
  NatTrans.congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac K

/-- The isomorphism `L F ≅ L G` induced by an isomorphism `e : F ≅ G` of exact functors is
compatible with the counits: on `Qh K` it is induced by `e` on the homotopy categories. -/
@[reassoc]
lemma leftDerivedFunctorNatIso_hom_app_Qh {G : C ⥤ D} [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (F.leftDerivedFunctorNatIso e).hom.app (DerivedCategory.Qh.obj K) ≫
        G.leftDerivedFunctorCounit.app K =
      F.leftDerivedFunctorCounit.app K ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K) := by
  rw [← G.leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh,
    ← F.leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh_assoc,
    ← mapDerivedCategoryNatIso_fach]
  simp [leftDerivedFunctorNatIso]

/-- The identification `L(𝟭) ≅ D(𝟭) ≅ 𝟭` is the counit of `L(𝟭)` on `Qh K`. -/
lemma leftDerivedFunctorIsoMapDerivedCategory_trans_mapDerivedCategoryIdIso_hom_app_Qh
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    ((𝟭 C).leftDerivedFunctorIsoMapDerivedCategory ≪≫ mapDerivedCategoryIdIso C).hom.app
        (DerivedCategory.Qh.obj K) = (𝟭 C).leftDerivedFunctorCounit.app K := by
  have h := congrArg (fun e ↦ e.hom.app K) (mapDerivedCategoryIdIso_factorsh C)
  have h' : (mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Qh.obj K) =
      (𝟭 C).mapDerivedCategoryFactorsh.hom.app K := by
    simp only [mapHomotopyCategoryIdIso_hom_app_eq_id, Iso.trans_hom,
      NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app, rightUnitor_hom_app,
      isoWhiskerRight_hom, whiskerRight_app, leftUnitor_hom_app] at h
    erw [Category.comp_id, Category.comp_id, CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h
  rw [Iso.trans_hom, NatTrans.comp_app, h']
  exact leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh _ K

section Composition

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

/-- The composition isomorphism `L(F ⋙ G) ≅ LF ⋙ LG` of exact functors is compatible with the
counits: followed by the counits of `LF` and `LG`, it is the counit of `L(F ⋙ G)`. -/
@[reassoc]
lemma leftDerivedFunctorCompIso_hom_app_Qh (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (F.leftDerivedFunctorCompIso G).hom.app (DerivedCategory.Qh.obj K) ≫
        G.leftDerivedFunctor.map (F.leftDerivedFunctorCounit.app K) ≫
        G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
      (F ⋙ G).leftDerivedFunctorCounit.app K := by
  rw [← (F ⋙ G).leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh,
    ← G.leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh,
    ← F.leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh,
    ← mapDerivedCategoryCompIso_fach, mapHomotopyCategoryCompIso_refl_hom_app]
  simp only [leftDerivedFunctorCompIso, Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    whiskerRight_app, Iso.symm_hom, isoWhiskerLeft_hom, whiskerLeft_app, Category.assoc,
    Functor.map_comp]
  congr 2
  rw [← NatTrans.naturality_assoc]
  simp

/-- The isomorphism `LF ⋙ LG ≅ L(F ⋙ G) ≅ LH` induced by `e : F ⋙ G ≅ H` is, modulo the counits,
`e` on the homotopy categories. -/
@[reassoc]
lemma leftDerivedFunctorCompIso_symm_trans_natIso_hom_app_Qh (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] {H : C ⥤ E} [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ⋙ G ≅ H)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    ((F.leftDerivedFunctorCompIso G).symm ≪≫ (F ⋙ G).leftDerivedFunctorNatIso e).hom.app
        (DerivedCategory.Qh.obj K) ≫ H.leftDerivedFunctorCounit.app K =
      G.leftDerivedFunctor.map (F.leftDerivedFunctorCounit.app K) ≫
        G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app K) := by
  rw [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    leftDerivedFunctorNatIso_hom_app_Qh, ← leftDerivedFunctorCompIso_hom_app_Qh_assoc,
    Iso.inv_hom_id_app_assoc]
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  rfl

end Composition

end CategoryTheory.Functor
