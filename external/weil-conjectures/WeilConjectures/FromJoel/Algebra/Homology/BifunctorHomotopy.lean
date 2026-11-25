/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.FromJoel.CategoryTheory.QuotientTwo

/-!
# The action of bifunctors on homotopy categories

Supplement to `Mathlib.Algebra.Homology.BifunctorHomotopy`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

namespace CategoryTheory.Functor

open HomologicalComplex

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category C₁] [Category C₂] [Category D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂),
    HasMapBifunctor K₁ K₂ F c]

noncomputable def bifunctorMapHomotopyCategory :
    HomotopyCategory C₁ c₁ ⥤ HomotopyCategory C₂ c₂ ⥤ HomotopyCategory D c :=
  CategoryTheory.Quotient.lift₂ _ _
    ((postcompose₂.obj (HomotopyCategory.quotient D c)).obj
    (map₂HomologicalComplex F c₁ c₂ c)) (by
      rintro _ _ _ _ ⟨h₁⟩ K₂
      exact HomotopyCategory.eq_of_homotopy _ _ (mapBifunctorMapHomotopy₁ h₁ (𝟙 K₂) F c)) (by
      rintro K₁ _ _ _ _ ⟨h₂⟩
      exact HomotopyCategory.eq_of_homotopy _ _ (mapBifunctorMapHomotopy₂ (𝟙 K₁) h₂ F c))

noncomputable def whiskeringLeft₂BifunctorMapHomotopyCategoryIso :
    (((whiskeringLeft₂ _).obj (HomotopyCategory.quotient C₁ c₁)).obj
      (HomotopyCategory.quotient C₂ c₂)).obj (bifunctorMapHomotopyCategory F c₁ c₂ c) ≅
      ((postcompose₂.obj (HomotopyCategory.quotient D c)).obj
        (map₂HomologicalComplex F c₁ c₂ c)) :=
  Iso.refl _

noncomputable def quotientCompBifunctorMapHomotopyObjIso (K₁ : HomologicalComplex C₁ c₁) :
    HomotopyCategory.quotient _ _ ⋙ (F.bifunctorMapHomotopyCategory c₁ c₂ c).obj
      ((HomotopyCategory.quotient _ _).obj K₁) ≅
        (F.map₂HomologicalComplex c₁ c₂ c).obj K₁ ⋙
          HomotopyCategory.quotient _ _ := Iso.refl _

noncomputable def quotientCompBifunctorMapHomotopyFlipObjIso
    (K₂ : HomologicalComplex C₂ c₂) :
    HomotopyCategory.quotient _ _ ⋙ (F.bifunctorMapHomotopyCategory c₁ c₂ c).flip.obj
      ((HomotopyCategory.quotient _ _).obj K₂) ≅
        (F.map₂HomologicalComplex c₁ c₂ c).flip.obj K₂ ⋙
          HomotopyCategory.quotient _ _ := Iso.refl _

end CategoryTheory.Functor
