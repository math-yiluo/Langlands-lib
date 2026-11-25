/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerScalar

/-!
# Normalized systems of ordinary supported Cartier Kummer maps

Source: Stacks Project, Tags 03PL and 0A45; blueprint
sec-smooth-purity/sk-prop-sf-cbc/lem-amb-cartier-kummer-map.md
(auxiliary; not a blueprint node).

## Main definitions

* `supportedDerivedUnit`: the canonical derived unit.
* `supportedExactDerivedMap`: the existing exact-functor/Ext comparison in general form.
* `OrdinarySupportedKummerSystem`: relative, Chern, pullback and scalar normalizations.
* The class families and compatibility predicates keep the dependent fields compact.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u vC vD uC uD wC wD wE

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

-- Match the category-instance proofs captured in the recorded derived module category.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- The inverse-image/direct-image unit on the derived constant object.
Source: Stacks 0A45 (auxiliary; not a blueprint node). -/
@[irreducible]
def supportedDerivedUnit (A : Type (u + 1)) [CommRing A]
    {D T : Scheme.{u}} (i : D ⟶ T) :
    ordinaryFiniteUnit A T ⟶ (ordinaryFinitePushforward A i).obj (ordinaryFiniteUnit A D) :=
  Adjunction.derivedSingleUnit (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i)
    (ordinaryFiniteConstant A T) (ordinaryFiniteConstant A D)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).hom.app (ModuleCat.of A A))

/-- Realize an Ext class after the canonical exact-direct-image comparison.
This is the existing single-object comparison followed by the existing Ext realization.
Source: Stacks 0A45 (auxiliary; not a blueprint node). -/
@[irreducible]
def supportedExactDerivedMap {C : Type uC} {E : Type uD}
    [Category.{vC} C] [Category.{vD} E] [Abelian C] [Abelian E]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} E] [HasExt.{wE} E]
    [HasKInjectiveResolutions C] (F : C ⥤ E) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (X : C) (Y : E)
    (c : Ext (F.obj X) Y 2) :
    F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj X) ⟶
      ((DerivedCategory.singleFunctor E 0).obj Y)⟦(2 : ℤ)⟧ :=
  (F.singleFunctorCompRightDerivedFunctorIso.app X).hom ≫ c.hom

end AlgebraicGeometry.Etale
