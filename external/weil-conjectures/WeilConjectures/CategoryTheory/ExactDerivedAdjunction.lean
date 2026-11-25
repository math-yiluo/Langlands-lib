/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # The specified localization of an exact adjunction

Source: Stacks Project, Derived Categories, Tag 015F, and the termwise
exact-adjunction localization specified in `def-weil-exact-derived-adjunction`
(auxiliary; not a blueprint node).

The categories have independent object, morphism, and derived morphism universes.
The commutative squares are precisely the standard exact-functor factorizations;
`Adjunction.localization` uses the localized original unit and counit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uC uD vC vD wC wD v h w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

/-- Localize the actual termwise adjunction using the standard exact-functor
factorizations, with independent universes for both categories. Its unit and
counit are the original termwise unit and counit after localization and these
specified comparisons. Source: Stacks Tag 015F and the construction specified
by the node (auxiliary; not a blueprint node). -/
@[reducible]
def mapExactDerivedCategory
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    F.mapDerivedCategory ⊣ G.mapDerivedCategory :=
  letI : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨F.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨G.mapDerivedCategoryFactors.symm⟩
  (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory

end CategoryTheory.Adjunction

namespace SheafOfModules.OpenTensorNormalization

end SheafOfModules.OpenTensorNormalization
