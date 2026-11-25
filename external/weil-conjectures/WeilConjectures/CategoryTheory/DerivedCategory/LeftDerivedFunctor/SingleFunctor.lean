/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-!
# The functors induced on derived categories and the single-degree embeddings

For exact functors `F G : C ⥤ D` and `G' : D ⥤ E`, the identifications `D(F) ≅ D(G)` and
`D(F ⋙ G') ≅ D(F) ⋙ D(G')` (`Functor.mapDerivedCategoryNatIso`,
`Functor.mapDerivedCategoryCompIso`) are compatible with the identifications
`D(F)(X[0]) ≅ (F X)[0]` (`Functor.mapDerivedCategorySingleFunctor`): on an object placed in
degree zero they are the given isomorphisms placed in degree zero
(`Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor`,
`Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor`,
`Functor.mapDerivedCategoryNatIso_comp_hom_app_singleFunctor`). The same holds for
`Functor.leftDerivedFunctorNatIso` and `Functor.leftDerivedFunctorCompIso` through the
identifications `Functor.singleFunctorCompLeftDerivedFunctorIso`.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma mapDerivedCategorySingleFunctor_hom_app_eq (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (X : C) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app X =
      F.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C (.up ℤ) 0).obj X) ≫
        DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app X) := by
  rw [← F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app X,
    Iso.hom_inv_id_app_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma mapDerivedCategoryNatIso_hom_app_singleFunctor {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) (X : C) :
    (mapDerivedCategoryNatIso e).hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app X =
      (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (DerivedCategory.singleFunctor D 0).map (e.hom.app X) := by
  rw [mapDerivedCategorySingleFunctor_hom_app_eq, mapDerivedCategorySingleFunctor_hom_app_eq]
  erw [mapDerivedCategoryNatIso_fac_assoc e ((HomologicalComplex.single C (.up ℤ) 0).obj X)]
  rw [Category.assoc]
  congr 1
  rw [← DerivedCategory.Q.map_comp]
  change _ = _ ≫ DerivedCategory.Q.map _
  rw [← DerivedCategory.Q.map_comp]
  congr 1
  ext i
  by_cases hi : i = 0
  · subst hi
    have h' : e.hom.app (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X).X 0) =
        F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫ e.hom.app X ≫
          G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv := by
      rw [e.hom.naturality_assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id, Category.comp_id]
    simp only [mapHomologicalComplex_obj_X, comp_obj, mapCochainComplexSingleFunctor,
      HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f, h',
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl,
      Iso.refl_hom, map_id, Iso.refl_inv, Category.id_comp,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Category.assoc,
      CochainComplex.singleFunctors, CochainComplex.shiftFunctor_obj_X',
      HomologicalComplex.single_map_f_self]
    erw [G.map_id, Category.comp_id, Category.id_comp, Category.comp_id]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_tgt _ _

lemma mapDerivedCategoryCompIso_hom_app_singleFunctor (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (X : C) :
    (mapDerivedCategoryCompIso F G).inv.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) =
      ((F ⋙ G).mapDerivedCategorySingleFunctor 0).hom.app X := by
  rw [mapDerivedCategorySingleFunctor_hom_app_eq, mapDerivedCategorySingleFunctor_hom_app_eq,
    mapDerivedCategorySingleFunctor_hom_app_eq]
  rw [← mapDerivedCategoryCompIso_fac F G]
  erw [Functor.map_comp, Category.assoc]
  simp only [Category.assoc]
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
  have := G.mapDerivedCategoryFactors.hom.naturality
    ((F.mapCochainComplexSingleFunctor 0).hom.app X)
  erw [reassoc_of% this]
  refine congrArg (_ ≫ ·) ?_
  erw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  refine congrArg _ ?_
  ext i
  by_cases hi : i = 0
  · subst hi
    simp only [comp_obj, mapCochainComplexSingleFunctor, HomologicalComplex.comp_f,
      mapHomologicalComplex_map_f, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq, eqToIso_refl,
      Iso.refl_hom, map_id, Iso.refl_inv, Category.id_comp, mapHomologicalComplexCompIso,
      NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_id, NatTrans.id_app,
      HomologicalComplex.id_f, comp_map]
    erw [Functor.map_id]
    rfl
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_tgt _ _


/-- The composite of `D(H) ≅ D(F ⋙ G) ≅ D(F) ⋙ D(G)` with the identifications of the derived
functors on objects placed in degree zero is `e` placed in degree zero. -/
lemma mapDerivedCategoryNatIso_comp_hom_app_singleFunctor (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H] (e : H ≅ F ⋙ G) (X : C) :
    (mapDerivedCategoryNatIso e).hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        (mapDerivedCategoryCompIso F G).inv.app _ ≫
          G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
            (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) =
      (H.mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (DerivedCategory.singleFunctor E 0).map (e.hom.app X) := by
  rw [mapDerivedCategoryCompIso_hom_app_singleFunctor,
    mapDerivedCategoryNatIso_hom_app_singleFunctor]

end CategoryTheory.Functor

universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

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

lemma leftDerivedFunctorNatIso_hom_app_singleFunctor_obj
    (H F : C ⥤ E) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (e : H ≅ F) (X : C) :
    (leftDerivedFunctorNatIso H e).hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        (F.singleFunctorCompLeftDerivedFunctorIso).hom.app X =
      (H.singleFunctorCompLeftDerivedFunctorIso).hom.app X ≫
        (DerivedCategory.singleFunctor E 0).map (e.hom.app X) := by
  simp [leftDerivedFunctorNatIso, singleFunctorCompLeftDerivedFunctorIso,
    mapDerivedCategoryNatIso_hom_app_singleFunctor]

-- the `simp` call unfolds the compatibility isomorphisms
set_option linter.flexible false in
lemma leftDerivedFunctorCompIso_hom_app_singleFunctor_obj
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (X : C) :
    (leftDerivedFunctorCompIso F G).hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        G.leftDerivedFunctor.map ((F.singleFunctorCompLeftDerivedFunctorIso).hom.app X) ≫
          (G.singleFunctorCompLeftDerivedFunctorIso).hom.app (F.obj X) =
      ((F ⋙ G).singleFunctorCompLeftDerivedFunctorIso).hom.app X := by
  simp [leftDerivedFunctorCompIso, singleFunctorCompLeftDerivedFunctorIso]
  exact mapDerivedCategoryCompIso_hom_app_singleFunctor F G X

end CategoryTheory.Functor
