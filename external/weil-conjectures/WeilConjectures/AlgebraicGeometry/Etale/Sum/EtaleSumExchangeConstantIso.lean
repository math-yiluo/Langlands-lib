/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.ConstructibleSheaf.Defs

/-! # Canonical constants for exact derived pullback

Source: Stacks Project, Sites and Sheaves, Tag 0H7J; Derived Categories, Tag 015F
(blueprint: def-pur-etale-sum-exchange-constant-iso).

The existing constant comparison is preserved verbatim and isolated from its coherence proof.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical constant-sheaf identification for exact derived inverse image,
written using the existing single-functor and constant-sheaf comparisons.
Source: Stacks Project, Sites and Sheaves, Tag 0H7J; Derived Categories, Tag 015F
(blueprint: def-pur-etale-sum-exchange-constant-iso). -/
noncomputable def etaleSumExchangeConstantIso
    (A : Type (u + 1)) [CommRing A] {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A A))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
          (ModuleCat.of A A)) :=
  ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app (ModuleCat.of A A))

end AlgebraicGeometry.Etale
