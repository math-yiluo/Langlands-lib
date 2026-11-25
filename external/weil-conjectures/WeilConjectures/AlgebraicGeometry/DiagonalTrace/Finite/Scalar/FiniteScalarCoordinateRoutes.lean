/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Coefficient.FiniteCoefficientScalarComparison
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryCoordinateArrow
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryComparedClass
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralRootClass

/-! # Scalar transport of an arbitrary finite ordinary arrow

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: def-sfb-finite-scalar-coordinate-routes).
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
  finiteScalarComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Intrinsic arrows from the actual ordinary realized coefficient unit.
Source: exact ordinary coefficient realization
(blueprint: def-sfb-finite-scalar-coordinate-routes). -/
def FiniteScalarIntrinsicArrow (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) (Y : Scheme.reductionModules T (SpTowerShriek.B l E T n)) :=
  (DerivedCategory.singleFunctor _ 0).obj
      ((finiteOrdinaryRealization l E n T).obj
        ((finiteOrdinaryComparison (FiniteRing l E n) T).obj
          (Etale.ordinaryFiniteConstant (FiniteRing l E n) T))) ⟶
    ((DerivedCategory.singleFunctor _ 0).obj Y)⟦(2 : ℤ)⟧

/-- Additive comparison arrows from the ordinary coefficient unit after forgetting.
Source: exact coefficient forgetting and site comparison
(blueprint: def-sfb-finite-scalar-coordinate-routes). -/
def FiniteScalarAbelianArrow (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) (Y : DiagonalAb T) :=
  (DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((comparisonUpperStar AddCommGrpCat.{u + 1} T).obj
        ((Etale.moduleAbelianForget (FiniteRing l E n) T).obj
          (Etale.ordinaryFiniteConstant (FiniteRing l E n) T))) ⟶
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).obj Y)⟦(2 : ℤ)⟧

/-- Integral-source arrows to an arbitrary additive target after normalization.
Source: the evaluated integer tower
(blueprint: def-sfb-finite-scalar-coordinate-routes). -/
def FiniteScalarIntegralArrow (n : ℕ) (T : Scheme.{u}) (Y : DiagonalAb T) :=
  (DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((abEvaluation T n).obj (integers T)) ⟶
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).obj Y)⟦(2 : ℤ)⟧

/-- Relation expressing the exact scalar comparison of two normalized arrows.
Source: exact coefficient forgetting and site comparison
(blueprint: def-sfb-finite-scalar-coordinate-routes). -/
def FiniteScalarTransportRelation (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {Y : Scheme.reductionModules T (SpTowerShriek.B l E T n)}
    {Y₀ : DiagonalAb T} (a : FiniteScalarIntrinsicArrow l E n T Y)
    (d : FiniteScalarAbelianArrow l E n T Y₀)
    (β : Y₀ ≅ (finiteForget l E T n).obj Y) :=
  mapSingleArrow (finiteForget l E T n) (2 : ℤ) a =
    (DerivedCategory.singleFunctor (DiagonalAb T) 0).map
        ((finiteScalarComparison l E n T).app _).inv ≫ d ≫
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map β.hom)⟦(2 : ℤ)⟧'

/-- The actual Hom from evaluated integers to the forgotten finite line.
Source: finite scalar coefficient coordinates
(blueprint: def-sfb-finite-scalar-coordinate-routes). -/
def FiniteScalarBoundaryArrow (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) :=
  (DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((abEvaluation T n).obj (integers T)) ⟶
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).obj
      ((finiteForget l E T n).obj (finiteLine l E T n)))⟦(2 : ℤ)⟧

/-- Normalize the module route by the actual finite quotient.
Source: finite scalar coefficient coordinates
(blueprint: def-sfb-finite-scalar-coordinate-routes). -/
def finiteScalarNormalizedModuleRoute (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT)
    (a : Etale.ordinaryFiniteUnit (FiniteRing l E n) T ⟶
      (Etale.ordinaryFiniteLine (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) T)⟦(2 : ℤ)⟧) :
    FiniteScalarBoundaryArrow l E n T :=
  (DerivedCategory.singleFunctor (DiagonalAb T) 0).map (finiteQuotient l E T n) ≫
        mapSingleArrow (finiteForget l E T n) (2 : ℤ)
          (finiteOrdinaryCoordinateArrow l E n T c a)

/-- Normalize the additive route by the integral generator and scalar line coordinate.
Source: exact site comparison and coefficient coordinates
(blueprint: def-sfb-finite-scalar-coordinate-routes). -/
def finiteScalarNormalizedAbelianRoute (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT)
    (a : Etale.ordinaryFiniteUnit (FiniteRing l E n) T ⟶
      (Etale.ordinaryFiniteLine (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) T)⟦(2 : ℤ)⟧) :
    FiniteScalarBoundaryArrow l E n T :=
  (DerivedCategory.singleFunctor (DiagonalAb T) 0).map (integerComparison T).inv ≫
        (DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          ((comparisonUpperStar AddCommGrpCat.{u + 1} T).map
            (Etale.ordinaryFiniteIntegralGenerator (FiniteRing l E n) T)) ≫
        finiteOrdinaryAbelianImage l E n T a ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (finiteScalarLineCoordinate l E n T c))⟦(2 : ℤ)⟧'

/-- Normalize the actual comparison image of any additive cohomology class
at the finite line endpoint. Source: the given integer and scalar line coordinates
(blueprint: def-sfb-finite-scalar-coordinate-routes). -/
def finiteScalarNormalizedCohomologyRoute (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT)
    (b : Sheaf.H ((Etale.moduleAbelianForget (FiniteRing l E n) T).obj
      (Scheme.finiteEtaleTateLine T (l ^ (n + 1)) (FiniteRing l E n)
        (ULift.ext (coefficient_annihilates l E n)))) 2) :
    FiniteScalarBoundaryArrow l E n T :=
  (DerivedCategory.singleFunctor (DiagonalAb T) 0).map (integerComparison T).inv ≫
    ordinaryFiniteComparedCohomologyClass (FiniteRing l E n) T
      (Scheme.finiteEtaleTateLine T (l ^ (n + 1)) (FiniteRing l E n)
        (ULift.ext (coefficient_annihilates l E n))) b ≫
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
      (finiteScalarLineCoordinate l E n T c))⟦(2 : ℤ)⟧'

/-- Normalize the actual compared ordinary scalar class at both endpoints.
Source: exact additive comparison and the specified finite line coordinate
(blueprint: def-sfb-finite-scalar-coordinate-routes). -/
def finiteScalarNormalizedClassRoute (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT)
    (a : Etale.ordinaryFiniteUnit (FiniteRing l E n) T ⟶
      (Etale.ordinaryFiniteLine (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) T)⟦(2 : ℤ)⟧) :
    FiniteScalarBoundaryArrow l E n T :=
  finiteScalarNormalizedCohomologyRoute l E n T c
    (Etale.ordinaryFiniteClass (FiniteRing l E n) T
      (Scheme.finiteEtaleTateLine T (l ^ (n + 1)) (FiniteRing l E n)
        (ULift.ext (coefficient_annihilates l E n))) 2 a)

/-- The normalized finite scalar image of an arbitrary integral root class.
Source: the integral roots comparison and finite root insertion
(blueprint: def-sfb-finite-scalar-coordinate-routes). -/
def finiteScalarNormalizedRootRoute (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) (x : Sheaf.H (T.rootsOfUnitySheaf (l ^ (n + 1))) 2) :
    FiniteScalarBoundaryArrow l E n T :=
  finiteIntegralRootClass l T n x ≫
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
      (finiteRootMap l E T n))⟦(2 : ℤ)⟧'

end AlgebraicGeometry.ProEtale.DiagonalTrace
