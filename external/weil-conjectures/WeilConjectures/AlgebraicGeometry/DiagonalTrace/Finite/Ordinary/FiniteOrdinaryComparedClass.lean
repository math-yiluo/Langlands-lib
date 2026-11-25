/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralCategoryWitnesses

/-! # The actual compared ordinary scalar class

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: def-sfb-finite-ordinary-compared-class).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃ t₁ t₂ t₃
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance 100000] Etale.ordinaryFiniteDerivedCategoryInstance
attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors

attribute [local instance 100001] finiteIntegralAbDerived finiteIntegralAbExt
  finiteIntegralEtaleDerived finiteIntegralEtaleExt

/-- The actual Hom of a compared additive ordinary cohomology class.
Source: exact additive site comparison
(blueprint: def-sfb-finite-ordinary-compared-class). -/
def OrdinaryFiniteComparedClassArrow (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  (DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ⟶
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        ((Etale.moduleAbelianForget A T).obj M)))⟦(2 : ℤ)⟧

/-- Exact comparison of an arbitrary additive class at the ordinary endpoint.
Source: exact additive site comparison
(blueprint: def-sfb-finite-ordinary-compared-class). -/
def ordinaryFiniteComparedCohomologyClass (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (b : Sheaf.H ((Etale.moduleAbelianForget A T).obj M) 2) :
    OrdinaryFiniteComparedClassArrow A T M :=
  mapSingleArrow (comparisonUpperStar AddCommGrpCat.{u + 1} T) (2 : ℤ) b.hom

end AlgebraicGeometry.ProEtale.DiagonalTrace
