/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-!
# Compatibility of the derived natural and composition isomorphisms with the counits

For exact functors `F` and `G` between abelian categories with functorial flat resolutions, the
isomorphisms `Functor.leftDerivedFunctorNatIso` and `Functor.leftDerivedFunctorCompIso` of
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory` are
compatible with the counits `Qh ⋙ L(F) ⟶ F ⋙ Qh` of the left derived functors. Since these
counits are isomorphisms for exact functors, this characterizes both isomorphisms.

## Main statements

- `CategoryTheory.Functor.leftDerivedFunctorNatIso_hom_app_comp_counit`
- `CategoryTheory.Functor.leftDerivedFunctorCompIso_hom_app_comp_counit`
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

/-- The component form of `Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac`. -/
@[reassoc]
lemma leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    F.leftDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Qh.obj K) ≫
        F.mapDerivedCategoryFactorsh.hom.app K = F.leftDerivedFunctorCounit.app K :=
  NatTrans.congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac K

/-- The isomorphism `L(F) ≅ L(G)` induced by an isomorphism `e : F ≅ G` of exact functors is
compatible with the counits:
```
Qh ⋙ L(F) ──e──▶ Qh ⋙ L(G)
    │                │
 counit           counit
    ▼                ▼
F ⋙ Qh ────e────▶ G ⋙ Qh
``` -/
@[reassoc]
lemma leftDerivedFunctorNatIso_hom_app_comp_counit {G : C ⥤ D} [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (F.leftDerivedFunctorNatIso e).hom.app (DerivedCategory.Qh.obj K) ≫
        G.leftDerivedFunctorCounit.app K =
      F.leftDerivedFunctorCounit.app K ≫ DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K) := by
  rw [← G.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac,
    ← F.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac_assoc]
  simp only [leftDerivedFunctorNatIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, mapDerivedCategoryNatIso_fach]

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

/-- The composition isomorphism `L(F ⋙ G) ≅ L(F) ⋙ L(G)` of exact functors is compatible with
the counits:
```
L(F ⋙ G)(Qh K) ──≅──▶ L(G)(L(F)(Qh K)) ──L(G)(counit)──▶ L(G)(Qh (F K)) ──counit──▶ Qh (G (F K))
       │                                                                                ‖
    counit                                                                              ‖
       ▼                                                                                ‖
Qh ((F ⋙ G) K) ═════════════════════════════════════════════════════════════════════ Qh (G (F K))
``` -/
@[reassoc]
lemma leftDerivedFunctorCompIso_hom_app_comp_counit (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (F.leftDerivedFunctorCompIso G).hom.app (DerivedCategory.Qh.obj K) ≫
        G.leftDerivedFunctor.map (F.leftDerivedFunctorCounit.app K) ≫
          G.leftDerivedFunctorCounit.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
      (F ⋙ G).leftDerivedFunctorCounit.app K := by
  have h := mapDerivedCategoryCompIso_fach F G K
  rw [mapHomotopyCategoryCompIso_refl_hom_app] at h
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at h
  rw [← G.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac,
    ← F.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac,
    ← (F ⋙ G).leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac, ← h]
  simp only [leftDerivedFunctorCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, isoWhiskerLeft_hom, whiskerLeft_app, Category.assoc,
    Functor.map_comp]
  rw [← NatTrans.naturality_assoc G.leftDerivedFunctorIsoMapDerivedCategory.inv,
    ← NatTrans.naturality_assoc G.leftDerivedFunctorIsoMapDerivedCategory.inv]
  simp only [comp_obj, Iso.inv_hom_id_app_assoc, ← G.mapDerivedCategory.map_comp_assoc]

end Composition

end CategoryTheory.Functor
