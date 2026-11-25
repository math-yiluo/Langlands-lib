/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory

/-! # Canonical pullback of diagonal coefficient diagrams

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-exchange).

## Main definitions

- `derivedUpper`: the actual derived coefficient inverse image.
- `ordinaryExchange`, `derivedExchange`: the canonical adjunction mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The actual derived inverse image, named once to share its derived-category
instances in the canonical exchange maps. Source: blueprint base-change clause
(blueprint: def-sfb-diagonal-coefficient-exchange). -/
def derivedUpper (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S) :
    DerivedCategory (Modules R S) ⥤ DerivedCategory (Modules R X) :=
  (CondensedRing.upperStar R f).leftDerivedFunctor

/-- The actual derived direct image, named once to share its derived-category
and K-injective-resolution instances in the model comparisons.
Source: blueprint base-change clause
(blueprint: def-sfb-diagonal-coefficient-exchange). -/
def derivedLower (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S) :
    DerivedCategory (Modules R X) ⥤ DerivedCategory (Modules R S) :=
  (CondensedRing.lowerStar R f).rightDerivedFunctor

/-- The inverse-image shift structure from its actual derived adjunction.
Source: blueprint base-change comparisons
(blueprint: def-sfb-diagonal-coefficient-exchange). -/
instance derivedUpperCommShift (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S) :
    (derivedUpper R f).CommShift ℤ :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction R f).leftAdjointCommShift ℤ

/-- The canonical Beck--Chevalley map is the mate of the compositional
pullback isomorphism of the specified commutative square. No proper or flat
base-change theorem is built into its definition. Source: blueprint clause 3
(blueprint: def-sfb-diagonal-coefficient-exchange). -/
def ordinaryExchange (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f) :
    CondensedRing.lowerStar R f ⋙ CondensedRing.upperStar R hS ⟶
      CondensedRing.upperStar R hX ⋙ CondensedRing.lowerStar R f' :=
  Adjunction.exchangeRight
    (G := CondensedRing.upperStar R hS) (G' := CondensedRing.upperStar R hX)
    (CondensedRing.upperStarLowerStarAdjunction R f)
    (CondensedRing.upperStarLowerStarAdjunction R f')
    (((CondensedRing.upperStarComp R f' hS).symm ≪≫
      CondensedRing.upperStarCongr R h ≪≫
      CondensedRing.upperStarComp R hX f))

/-- The corresponding derived mate, with the same composition normalization.
Source: blueprint clause 3 (blueprint: def-sfb-diagonal-coefficient-exchange). -/
def derivedExchange (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f) :
    (derivedLower R f) ⋙
        (derivedUpper R hS) ⟶
      (derivedUpper R hX) ⋙
        (derivedLower R f') :=
  Adjunction.exchangeRight
    (G := derivedUpper R hS) (G' := derivedUpper R hX)
    (CondensedRing.derivedUpperStarLowerStarAdjunction R f)
    (CondensedRing.derivedUpperStarLowerStarAdjunction R f')
    (((CondensedRing.leftDerivedUpperStarComp R f' hS).symm ≪≫
      Functor.leftDerivedFunctorNatIso _ (CondensedRing.upperStarCongr R h) ≪≫
      CondensedRing.leftDerivedUpperStarComp R hX f))

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
