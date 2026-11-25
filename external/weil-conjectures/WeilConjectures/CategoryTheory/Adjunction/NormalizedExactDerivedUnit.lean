/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement

/-! # The unit of an exact derived adjunction on every complex

The standard termwise comparisons are fixed throughout the equation.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
universe uC uD vC vD wC wD

set_option autoImplicit false

namespace CategoryTheory.Adjunction
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Under the standard exact-functor comparisons, the derived unit is the
localization of the termwise ordinary unit, on every complex.
Source: Stacks Tag 015F and Mathlib localization of adjunctions.
(blueprint: lem-weil-pbc-normalized-exact-derived-unit).

Proof: use the component formula for the localized adjunction's unit. Its two
comparison inverses cancel the specified forward comparisons, leaving precisely
the localization of the termwise unit. No resolution or boundedness is needed. -/
theorem mapExactDerivedCategory_unit (a : F ⊣ G) (P : CochainComplex C ℤ) :
    a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex a.unit (.up ℤ)).app P) := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactors.symm⟩
  rw [mapExactDerivedCategory, localization_unit_app]
  change (_ ≫ G.mapDerivedCategoryFactors.inv.app _ ≫
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app P)) ≫ _ ≫ _ = _
  simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [G.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app,
    Category.comp_id]
  rfl

end CategoryTheory.Adjunction
