/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompExact
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Compatibility of the comparison isomorphisms of left derived functors with the counits

The comparison isomorphisms between total left derived functors computed via K-flat resolutions
(`Functor.leftDerivedFunctorCompMapDerivedCategoryIso`,
`Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso`, `Functor.leftDerivedFunctorIsoOfIso`)
are all induced by the universal property of left derived functors. This file records their
compatibility with the counits `Qh ⋙ L(G) ⟶ G.mapHomotopyCategory ⋙ Qh`, component by component.

-/

@[expose] public section

universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]

/-- `Functor.leftDerivedFunctorIsoOfIso` is compatible with the counits. -/
@[reassoc]
lemma leftDerivedFunctorIsoOfIso_hom_app_comp_counit {G G' : C ⥤ D} [G.Additive] [G'.Additive]
    [G.PreservesKFlatQuasiIso] [G'.PreservesKFlatQuasiIso] (e : G ≅ G')
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (leftDerivedFunctorIsoOfIso e).hom.app (DerivedCategory.Qh.obj K) ≫
        G'.leftDerivedFunctorCounit.app K =
      G.leftDerivedFunctorCounit.app K ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K) := by
  simp [leftDerivedFunctorIsoOfIso]

/-- For an exact functor, `Functor.leftDerivedFunctorIsoMapDerivedCategory` followed by the
comparison `Functor.mapDerivedCategoryFactorsh` is the counit. -/
@[reassoc]
lemma leftDerivedFunctorIsoMapDerivedCategory_hom_app_comp_factorsh (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj K) ≫
        F.mapDerivedCategoryFactorsh.hom.app K =
      F.leftDerivedFunctorCounit.app K := by
  rw [← F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac, NatTrans.comp_app,
    Functor.whiskerLeft_app]

/-- For an exact functor, `Functor.leftDerivedFunctorIsoMapDerivedCategory` on the image of a
complex, compared with the factorization `Functor.mapDerivedCategoryFactors` through `Q`, is the
counit. -/
@[reassoc]
lemma leftDerivedFunctorIsoMapDerivedCategory_hom_app_quotient_obj (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (Z : CochainComplex C ℤ) :
    F.leftDerivedFunctorIsoMapDerivedCategory.hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Z)) ≫
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app Z) ≫
      F.mapDerivedCategoryFactors.hom.app Z =
    F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Z) ≫
      (DerivedCategory.quotientCompQhIso D).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) := by
  rw [← leftDerivedFunctorIsoMapDerivedCategory_hom_app_comp_factorsh,
    mapDerivedCategoryFactorsh_hom_app]
  simp [mapHomotopyCategoryFactors]

/-- For an exact functor, the inverse of `Functor.leftDerivedFunctorIsoMapDerivedCategory`
followed by the counit is the comparison `Functor.mapDerivedCategoryFactorsh`. -/
@[reassoc]
lemma leftDerivedFunctorIsoMapDerivedCategory_inv_app_comp_counit (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    F.leftDerivedFunctorIsoMapDerivedCategory.inv.app (DerivedCategory.Qh.obj K) ≫
        F.leftDerivedFunctorCounit.app K =
      F.mapDerivedCategoryFactorsh.hom.app K := by
  rw [← F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]

section CompRight

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  (G : C ⥤ D) [G.Additive] [G.PreservesKFlatQuasiIso]
  (F' : D ⥤ E) [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']

/-- `Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso` is compatible with the counits. -/
@[reassoc]
lemma leftDerivedFunctorCompMapDerivedCategoryRightIso_hom_app_comp_counit
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (leftDerivedFunctorCompMapDerivedCategoryRightIso G F').hom.app (DerivedCategory.Qh.obj K) ≫
        F'.mapDerivedCategory.map (G.leftDerivedFunctorCounit.app K) ≫
        F'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (G ⋙ F')) (ComplexShape.up ℤ)).hom.app K) =
      (G ⋙ F').leftDerivedFunctorCounit.app K := by
  have h := leftDerivedNatTrans_app (G ⋙ F').leftDerivedFunctor
    (G.leftDerivedFunctor ⋙ F'.mapDerivedCategory) (G ⋙ F').leftDerivedFunctorCounit
    (leftDerivedFunctorCompMapDerivedCategoryRightCounit G F')
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) (𝟙 _) K
  simp only [NatTrans.id_app, Category.comp_id] at h
  rw [← h]
  simp [leftDerivedFunctorCompMapDerivedCategoryRightIso,
    leftDerivedFunctorCompMapDerivedCategoryRightCounit]

end CompRight

section CompositionKFlat

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : D ⥤ E) [G.Additive] [G.PreservesKFlatQuasiIso] [F.PreservesKFlatComplexes]

/-- `Functor.leftDerivedFunctorCompMapDerivedCategoryIso` is compatible with the counits. -/
@[reassoc]
lemma leftDerivedFunctorCompMapDerivedCategoryIso_hom_app_comp_counit
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (leftDerivedFunctorCompMapDerivedCategoryIso F G).hom.app (DerivedCategory.Qh.obj K) ≫
        G.leftDerivedFunctor.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app K) =
      (F ⋙ G).leftDerivedFunctorCounit.app K := by
  have h := leftDerivedNatTrans_app (F ⋙ G).leftDerivedFunctor
    (F.mapDerivedCategory ⋙ G.leftDerivedFunctor) (F ⋙ G).leftDerivedFunctorCounit
    (leftDerivedFunctorCompMapDerivedCategoryCounit F G)
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) (𝟙 _) K
  simp only [NatTrans.id_app, Category.comp_id] at h
  rw [← h]
  simp [leftDerivedFunctorCompMapDerivedCategoryIso,
    leftDerivedFunctorCompMapDerivedCategoryCounit]

/-- The inverse of `Functor.leftDerivedFunctorCompMapDerivedCategoryIso` is compatible with the
counits. -/
@[reassoc]
lemma leftDerivedFunctorCompMapDerivedCategoryIso_inv_app_comp_counit
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (leftDerivedFunctorCompMapDerivedCategoryIso F G).inv.app (DerivedCategory.Qh.obj K) ≫
        (F ⋙ G).leftDerivedFunctorCounit.app K =
      G.leftDerivedFunctor.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom.app K) := by
  rw [← cancel_epi ((leftDerivedFunctorCompMapDerivedCategoryIso F G).hom.app _),
    Iso.hom_inv_id_app_assoc, leftDerivedFunctorCompMapDerivedCategoryIso_hom_app_comp_counit]

end CompositionKFlat


/-- **The left derived functor of an exact functor and the connecting morphisms of short exact
sequences**: for an exact functor `F` whose left derived functor commutes with the shifts
compatibly with `Functor.leftDerivedFunctorIsoMapDerivedCategory`, `L(F)` of the connecting
morphism of a short exact sequence of complexes `S` is, modulo the counits, the connecting
morphism of the image of `S`. -/
lemma leftDerivedFunctor_map_triangleOfSESδ (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [F.leftDerivedFunctor.CommShift ℤ]
    [NatTrans.CommShift F.leftDerivedFunctorIsoMapDerivedCategory.inv ℤ]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    F.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app S.X₃ ≫
        DerivedCategory.triangleOfSESδ hS ≫
        ((DerivedCategory.quotientCompQhIso C).inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
      (F.leftDerivedFunctor.commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj S.X₁)) ≫
      (F.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj S.X₁))⟦(1 : ℤ)⟧' =
    F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj S.X₃) ≫
      (DerivedCategory.quotientCompQhIso D).hom.app ((F.mapHomologicalComplex _).obj S.X₃) ≫
      DerivedCategory.triangleOfSESδ (hS.map_of_exact (F.mapHomologicalComplex _)) ≫
      ((DerivedCategory.quotientCompQhIso D).inv.app
        ((F.mapHomologicalComplex _).obj S.X₁))⟦(1 : ℤ)⟧' := by
  set e := F.leftDerivedFunctorIsoMapDerivedCategory
  have h₁ := e.inv.naturality ((DerivedCategory.quotientCompQhIso C).hom.app S.X₃ ≫
    DerivedCategory.triangleOfSESδ hS ≫
    ((DerivedCategory.quotientCompQhIso C).inv.app S.X₁)⟦(1 : ℤ)⟧')
  have h₂ := NatTrans.shift_app_comm e.inv (1 : ℤ)
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj S.X₁))
  have h₃ := DerivedCategory.map_triangleOfSESδ F hS
  have h₅ := leftDerivedFunctorIsoMapDerivedCategory_inv_app_comp_counit F
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj S.X₁)
  have h₆ := leftDerivedFunctorIsoMapDerivedCategory_inv_app_comp_counit F
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj S.X₃)
  rw [mapDerivedCategoryFactorsh_hom_app] at h₅ h₆
  rw [← cancel_epi (e.inv.app
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj S.X₃))),
    reassoc_of% h₆]
  dsimp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂ h₃ ⊢
  rw [← reassoc_of% h₁, ← reassoc_of% h₂, ← Functor.map_comp, h₅]
  simp only [Functor.map_comp, Category.assoc, mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  rw [← Functor.commShiftIso_hom_naturality_assoc, h₃]
  dsimp only [Functor.comp_obj]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  have hc : F.mapDerivedCategory.map
      (((DerivedCategory.quotientCompQhIso C).inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
      F.mapDerivedCategory.map (((DerivedCategory.quotientCompQhIso C).hom.app S.X₁)⟦(1 : ℤ)⟧') =
        𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
  have hc₂ : (F.mapDerivedCategoryFactors.inv.app S.X₁)⟦(1 : ℤ)⟧' ≫
      (F.mapDerivedCategoryFactors.hom.app S.X₁)⟦(1 : ℤ)⟧' = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, reassoc_of% hc, reassoc_of% hc₂]

section MapDerivedCategory

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Abelian C₁]
  [Abelian C₂] [Abelian C₃] [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]

/-- `Functor.mapDerivedCategoryNatIso_fach`, for the inverse. -/
@[reassoc]
lemma mapDerivedCategoryNatIso_inv_app_Qh_comp_factorsh {F G : C₁ ⥤ C₂} [F.Additive]
    [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (K : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    (mapDerivedCategoryNatIso e).inv.app (DerivedCategory.Qh.obj K) ≫
        F.mapDerivedCategoryFactorsh.hom.app K =
      G.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)).app K) := by
  rw [← cancel_epi ((mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Qh.obj K)),
    Iso.hom_inv_id_app_assoc, mapDerivedCategoryNatIso_fach_assoc, ← DerivedCategory.Qh.map_comp,
    ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
    NatTrans.mapHomotopyCategory_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- `Functor.mapDerivedCategoryCompIso_fach`, for the inverse. -/
@[reassoc]
lemma mapDerivedCategoryCompIso_inv_app_Qh_comp_factorsh (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    (mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Qh.obj K) ≫
        (F ⋙ G).mapDerivedCategoryFactorsh.hom.app K =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))
          (ComplexShape.up ℤ)).hom.app K) := by
  rw [← mapDerivedCategoryCompIso_fach, Iso.hom_inv_id_app_assoc]

end MapDerivedCategory

end CategoryTheory.Functor


namespace CategoryTheory.Functor

variable {V W V' : Type*} [Category* V] [Category* W] [Category* V'] [Preadditive V]
  [Preadditive W] [Preadditive V'] {ι : Type*} {c : ComplexShape ι}

/-- `Functor.mapHomotopyCategoryCompIso` on the image of a complex. -/
lemma mapHomotopyCategoryCompIso_hom_app_quotient_obj {F : V ⥤ W} {G : W ⥤ V'} {H : V ⥤ V'}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) (K : HomologicalComplex V c) :
    (mapHomotopyCategoryCompIso e c).hom.app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient V' c).map ((mapHomologicalComplexCompIso e c).hom.app K) :=
  rfl

/-- `Functor.mapHomotopyCategoryCompIso` on the image of a complex, for the inverse. -/
lemma mapHomotopyCategoryCompIso_inv_app_quotient_obj {F : V ⥤ W} {G : W ⥤ V'} {H : V ⥤ V'}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) (K : HomologicalComplex V c) :
    (mapHomotopyCategoryCompIso e c).inv.app ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient V' c).map ((mapHomologicalComplexCompIso e c).inv.app K) :=
  rfl

/-- The functor induced on homotopy categories, on the image of a complex. -/
lemma mapHomotopyCategory_obj_quotient_obj (F : V ⥤ W) [F.Additive] (K : HomologicalComplex V c) :
    (F.mapHomotopyCategory c).obj ((HomotopyCategory.quotient V c).obj K) =
      (HomotopyCategory.quotient W c).obj ((F.mapHomologicalComplex c).obj K) :=
  rfl


end CategoryTheory.Functor
