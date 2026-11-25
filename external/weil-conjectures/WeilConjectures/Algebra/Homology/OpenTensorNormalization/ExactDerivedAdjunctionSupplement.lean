/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Adjunction
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.ExactDerivedAdjunction

/-! # The specified localization of an exact adjunction

Source: Stacks Project, Derived Categories, Tag 015F, and the termwise
exact-adjunction localization specified in `def-weil-exact-derived-adjunction`
(blueprint: def-weil-exact-derived-adjunction).

The categories have independent object, morphism, and derived morphism universes.
The commutative squares are precisely the standard exact-functor factorizations;
`Adjunction.localization` uses the localized original unit and counit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uC uD vC vD wC wD v h w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

end CategoryTheory.Adjunction

namespace SheafOfModules.OpenTensorNormalization

/-- Localize the actual termwise adjunction, with the standard exact-functor
factorizations. Source: Stacks 015F.
(blueprint: lem-sf-open-tensor-normalization). -/
def exactDerivedAdjunction {C D : Type v} [Category.{h} C] [Category.{h} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    F.mapDerivedCategory ⊣ G.mapDerivedCategory :=
  a.mapExactDerivedCategory

end SheafOfModules.OpenTensorNormalization
