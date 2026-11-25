/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.MapHomologicalComplexHomologyIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-!
# Coherence of the commutation of exact functors with homology

For an exact functor `F` between abelian categories, the isomorphisms
`F.mapDerivedCategoryHomologyFunctorIso n : H^n(-) ⋙ F ≅ F.mapDerivedCategory ⋙ H^n(-)` and
`F.leftDerivedFunctorHomologyFunctorIso n : H^n(-) ⋙ F ≅ F.leftDerivedFunctor ⋙ H^n(-)`
are compatible with isomorphisms of functors and with the composition of functors:

- `Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_comp_map_mapDerivedCategoryCompIso` (the
  naturality in `F` is `Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_naturality`);
- `Functor.leftDerivedFunctorHomologyFunctorIso_hom_app_comp_map_leftDerivedFunctorNatIso`,
  `Functor.leftDerivedFunctorHomologyFunctorIso_hom_app_comp_map_leftDerivedFunctorCompIso`.

-/

@[expose] public section

universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section MapDerivedCategory

variable {C : Type uC} {D : Type uD} {E : Type uE} [Category.{vC} C] [Category.{vD} D]
  [Category.{vE} E] [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wE} E]

set_option backward.isDefEq.respectTransparency false in
/-- The composition isomorphism `Functor.mapDerivedCategoryCompIso` is compatible with the
factorizations `Functor.mapDerivedCategoryFactors` through the localization functors. -/
@[reassoc]
lemma mapDerivedCategoryFactors_inv_app_comp_mapDerivedCategoryCompIso_hom_app
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (L : CochainComplex C ℤ) :
    (F ⋙ G).mapDerivedCategoryFactors.inv.app L ≫
        (mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj L) =
      DerivedCategory.Q.map
          ((mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app L) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj L) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app L) := by
  have h := congrArg Iso.inv (Iso.ext (mapDerivedCategoryCompIso_fac F G L) :
    (mapDerivedCategoryCompIso F G).symm.app (DerivedCategory.Q.obj L) ≪≫
      G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app L) ≪≫
      G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj L) ≪≫
      DerivedCategory.Q.mapIso
        ((mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).app L) =
    (F ⋙ G).mapDerivedCategoryFactors.app L)
  simp only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, assoc] at h
  rw [← h]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `F.mapDerivedCategoryHomologyFunctorIso n` is compatible with the
composition of exact functors. -/
@[reassoc]
lemma mapDerivedCategoryHomologyFunctorIso_hom_app_comp_map_mapDerivedCategoryCompIso
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (n : ℤ) (K : DerivedCategory C) :
    ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.homologyFunctor E n).map ((mapDerivedCategoryCompIso F G).inv.app K) =
      G.map ((F.mapDerivedCategoryHomologyFunctorIso n).hom.app K) ≫
        (G.mapDerivedCategoryHomologyFunctorIso n).hom.app (F.mapDerivedCategory.obj K) := by
  have h := Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (τ := ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso n).hom ≫
      whiskerRight (mapDerivedCategoryCompIso F G).inv (DerivedCategory.homologyFunctor E n))
    (τ' := (whiskerRight (F.mapDerivedCategoryHomologyFunctorIso n).hom G ≫
      (associator _ _ _).hom ≫
      whiskerLeft F.mapDerivedCategory (G.mapDerivedCategoryHomologyFunctorIso n).hom ≫
      (associator _ _ _).inv :
        DerivedCategory.homologyFunctor C n ⋙ F ⋙ G ⟶
          (F.mapDerivedCategory ⋙ G.mapDerivedCategory) ⋙
            DerivedCategory.homologyFunctor E n)) (fun L ↦ by
      have hG := (G.mapDerivedCategoryHomologyFunctorIso n).hom.naturality
        (F.mapDerivedCategoryFactors.inv.app L)
      simp only [Functor.comp_map] at hG
      simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, associator_hom_app,
        associator_inv_app, id_comp, comp_id, mapDerivedCategoryHomologyFunctorIso_hom_app_Q,
        assoc, Functor.map_comp]
      rw [← Functor.map_comp,
        mapDerivedCategoryFactors_inv_app_comp_mapDerivedCategoryCompIso_hom_app,
        Functor.map_comp]
      erw [hG, mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
      have hn := (DerivedCategory.homologyFunctorFactors E n).inv.naturality
        ((mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app L)
      simp only [Functor.comp_map] at hn
      rw [Functor.map_comp, ← reassoc_of% hn,
        mapHomologicalComplexHomologyIso_inv_app_comp_map_compIso_inv_app_assoc]
      simp only [assoc, Iso.refl_inv, NatTrans.id_app, ← G.map_comp_assoc,
        Iso.inv_hom_id_app]
      erw [id_comp, comp_id]
      simp only [G.map_comp, assoc]
      rfl)
  simpa using congr_app h K

end MapDerivedCategory

open MonoidalCategory

section LeftDerivedFunctor

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

/-- The isomorphism `F.leftDerivedFunctorHomologyFunctorIso n` is natural in the exact
functor `F`. -/
@[reassoc]
lemma leftDerivedFunctorHomologyFunctorIso_hom_app_comp_map_leftDerivedFunctorNatIso
    {G : C ⥤ D} [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (n : ℤ) (K : DerivedCategory C) :
    (F.leftDerivedFunctorHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.homologyFunctor D n).map ((F.leftDerivedFunctorNatIso e).hom.app K) =
      e.hom.app ((DerivedCategory.homologyFunctor C n).obj K) ≫
        (G.leftDerivedFunctorHomologyFunctorIso n).hom.app K := by
  simp [leftDerivedFunctorHomologyFunctorIso, leftDerivedFunctorNatIso,
    ← mapDerivedCategoryHomologyFunctorIso_hom_app_naturality_assoc]

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

/-- The isomorphism `F.leftDerivedFunctorHomologyFunctorIso n` is compatible with the
composition of exact functors. -/
@[reassoc]
lemma leftDerivedFunctorHomologyFunctorIso_hom_app_comp_map_leftDerivedFunctorCompIso
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (n : ℤ)
    (K : DerivedCategory C) :
    ((F ⋙ G).leftDerivedFunctorHomologyFunctorIso n).hom.app K ≫
        (DerivedCategory.homologyFunctor E n).map ((F.leftDerivedFunctorCompIso G).hom.app K) =
      G.map ((F.leftDerivedFunctorHomologyFunctorIso n).hom.app K) ≫
        (G.leftDerivedFunctorHomologyFunctorIso n).hom.app (F.leftDerivedFunctor.obj K) := by
  have hG := (G.mapDerivedCategoryHomologyFunctorIso n).hom.naturality
    (F.leftDerivedFunctorIsoMapDerivedCategory.inv.app K)
  simp only [Functor.comp_map] at hG
  simp only [comp_obj, leftDerivedFunctorHomologyFunctorIso, Iso.trans_hom, isoWhiskerRight_hom,
    Iso.symm_hom, NatTrans.comp_app, whiskerRight_app, leftDerivedFunctorCompIso,
    isoWhiskerLeft_hom, whiskerLeft_app, NatTrans.naturality, map_comp, assoc, cancelIso,
    mapDerivedCategoryHomologyFunctorIso_hom_app_comp_map_mapDerivedCategoryCompIso_assoc,
    reassoc_of% hG]
  congr 2
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (G.leftDerivedFunctorIsoMapDerivedCategory.inv.naturality _).symm

end Composition

end LeftDerivedFunctor

end CategoryTheory.Functor
