/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryCoefficientModel
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralCategoryWitnesses

/-! # The actual transported ordinary arrows

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: def-sfb-finite-ordinary-transport-images).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃ t₁ t₂ t₃
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance 100001] finiteOrdinaryDerived finiteOrdinaryExt
  finiteOrdinaryIntrinsicDerived
  finiteIntegralAbDerived finiteIntegralAbExt finiteIntegralEtaleDerived finiteIntegralEtaleExt
attribute [local instance 100000] Etale.ordinaryFiniteDerivedCategoryInstance

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
attribute [local implicit_reducible] SpTowerShriek.tau spCoefficientCommRings
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  Etale.ordinaryFiniteDegreeZero Etale.ordinaryFiniteSingleFunctor
  diagonalAbSheafAbelian towerAbelian systemsAbelian

attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Hom type for the actual comparison-realization image of ordinary endpoints.
Source: exact coefficient comparison and intrinsic realization
(blueprint: def-sfb-finite-ordinary-transport-images). -/
def FiniteOrdinaryIntrinsicImageArrow (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) (M N : OrdinaryEtaleModules (FiniteRing l E n) T) :=
  (DerivedCategory.singleFunctor _ 0).obj
      ((finiteOrdinaryRealization l E n T).obj
        ((finiteOrdinaryComparison (FiniteRing l E n) T).obj M)) ⟶
    ((DerivedCategory.singleFunctor _ 0).obj
      ((finiteOrdinaryRealization l E n T).obj
        ((finiteOrdinaryComparison (FiniteRing l E n) T).obj N)))⟦(2 : ℤ)⟧

/-- Hom type for the actual forgotten ordinary endpoints after additive comparison.
Source: exact scalar forgetting and additive site comparison
(blueprint: def-sfb-finite-ordinary-transport-images). -/
def FiniteOrdinaryAbelianImageArrow (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) (M N : OrdinaryEtaleModules (FiniteRing l E n) T) :=
  (DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        ((Etale.moduleAbelianForget (FiniteRing l E n) T).obj M)) ⟶
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        ((Etale.moduleAbelianForget (FiniteRing l E n) T).obj N)))⟦(2 : ℤ)⟧

/-- The comparison-realization image of the given ordinary derived arrow.
Source: exact coefficient comparison and intrinsic realization
(blueprint: def-sfb-finite-ordinary-transport-images). -/
def finiteOrdinaryIntrinsicImage (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {M N : OrdinaryEtaleModules (FiniteRing l E n) T}
    (a : (DerivedCategory.singleFunctor _ 0).obj M ⟶
      ((DerivedCategory.singleFunctor _ 0).obj N)⟦(2 : ℤ)⟧) :
    FiniteOrdinaryIntrinsicImageArrow l E n T M N :=
  mapSingleArrow (finiteOrdinaryRealization l E n T) (2 : ℤ)
    (mapSingleArrow (finiteOrdinaryComparison (FiniteRing l E n) T) (2 : ℤ) a)

/-- The additive comparison image of the ordinary arrow after forgetting scalars.
Source: exact scalar forgetting and additive site comparison
(blueprint: def-sfb-finite-ordinary-transport-images). -/
def finiteOrdinaryAbelianImage (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {M N : OrdinaryEtaleModules (FiniteRing l E n) T}
    (a : (DerivedCategory.singleFunctor _ 0).obj M ⟶
      ((DerivedCategory.singleFunctor _ 0).obj N)⟦(2 : ℤ)⟧) :
    FiniteOrdinaryAbelianImageArrow l E n T M N :=
  mapSingleArrow (comparisonUpperStar AddCommGrpCat.{u + 1} T) (2 : ℤ)
    (mapSingleArrow (Etale.moduleAbelianForget (FiniteRing l E n) T) (2 : ℤ) a)

end AlgebraicGeometry.ProEtale.DiagonalTrace
