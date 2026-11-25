/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction

/-!
# The unit and counit of the levelwise derived adjunction

For an adjunction `adj : f ⊣ g` of exact functors between abelian categories, the unit of the
levelwise derived adjunction `f.mapDerivedCategory ⊣ g.mapDerivedCategory`
(`CategoryTheory.Adjunction.mapDerivedCategoryAdjunction`) is, on the image `Qh X` of an object
of the homotopy category, the image of the unit of the adjunction induced on homotopy categories
(`CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_unit_app_Qh_obj`), and likewise for the
counit (`CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_counit_app_Qh_obj`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Abelian

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g) [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]

/-- On the image `Qh X` of an object of the homotopy category, the unit of the levelwise derived
adjunction `D(f) ⊣ D(g)` is the image of the unit of the adjunction induced on homotopy
categories:
```
  Qh X ──────unit──────▶ D(g) D(f) (Qh X)
      ╲                        │ D(g)(≅) ≫ ≅
       ╲ Qh(unit)              ▼
        ╲──────────────▶ Qh (g (f X))
```
-/
@[reassoc]
lemma mapDerivedCategoryAdjunction_unit_app_Qh_obj (X : HomotopyCategory C (.up ℤ)) :
    adj.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj X) ≫
        g.mapDerivedCategory.map (f.mapDerivedCategoryFactorsh.hom.app X) ≫
        g.mapDerivedCategoryFactorsh.hom.app ((f.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app X) := by
  have h₁ := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) f.leftDerivedFunctorCounit g.rightDerivedFunctorUnit X
  have h₂ := NatTrans.congr_app f.leftDerivedFunctorIsoMapDerivedCategory_hom_fac X
  have h₃ := NatTrans.congr_app g.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((f.mapHomotopyCategory (.up ℤ)).obj X)
  have h₄ := g.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (f.mapDerivedCategoryFactorsh.hom.app X)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj] at h₁ h₂ h₃ h₄
  simp only [mapDerivedCategoryAdjunction, ofNatIsoRight_unit, ofNatIsoLeft_unit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
  rw [← reassoc_of% h₄, ← Functor.map_comp_assoc, h₂]
  erw [reassoc_of% h₁]
  rw [reassoc_of% h₃, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- On the image `Qh X` of an object of the homotopy category, the counit of the levelwise
derived adjunction `D(f) ⊣ D(g)` is the image of the counit of the adjunction induced on homotopy
categories:
```
  D(f) D(g) (Qh X) ──D(f)(≅) ≫ ≅──▶ Qh (f (g X)) ──Qh(counit)──▶ Qh X
```
-/
lemma mapDerivedCategoryAdjunction_counit_app_Qh_obj (X : HomotopyCategory D (.up ℤ)) :
    adj.mapDerivedCategoryAdjunction.counit.app (DerivedCategory.Qh.obj X) =
      f.mapDerivedCategory.map (g.mapDerivedCategoryFactorsh.hom.app X) ≫
        f.mapDerivedCategoryFactorsh.hom.app ((g.mapHomotopyCategory (.up ℤ)).obj X) ≫
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app X) := by
  have h₁ := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso D (.up ℤ)) f.leftDerivedFunctorCounit g.rightDerivedFunctorUnit X
  have h₂ := NatTrans.congr_app f.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((g.mapHomotopyCategory (.up ℤ)).obj X)
  have h₃ := NatTrans.congr_app g.rightDerivedFunctorIsoMapDerivedCategory_hom_fac X
  have h₄ := f.leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
    (g.rightDerivedFunctorUnit.app X)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj] at h₁ h₂ h₃ h₄
  have h₃' : g.rightDerivedFunctorIsoMapDerivedCategory.inv.app (DerivedCategory.Qh.obj X) =
      g.mapDerivedCategoryFactorsh.hom.app X ≫ g.rightDerivedFunctorUnit.app X := by
    rw [← cancel_mono (g.rightDerivedFunctorIsoMapDerivedCategory.hom.app _),
      Iso.inv_hom_id_app, Category.assoc, h₃, Iso.hom_inv_id_app]
    rfl
  simp only [mapDerivedCategoryAdjunction, ofNatIsoRight_counit, ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [h₃', Functor.map_comp, Category.assoc, reassoc_of% h₄, derivedAdjunction, derived_counit,
    h₁, ← reassoc_of% h₂, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Adjunction
