/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Scalar.FiniteScalarCoordinateRoutes
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryScalarClassImage

/-! # Scalar transport of an arbitrary finite ordinary arrow

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-scalar-class-route-equation).
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

/-- Realizing the ordinary scalar class identifies the two normalized
additive routes. Source: exact scalar-class realization and associativity
(blueprint: lem-sfb-finite-scalar-class-route-equation).

Proof: specialize ordinaryFiniteClass_exact_image_prepost to additive site
comparison, integerComparison.inv and the shifted scalar line coordinate.
All middle arrows are the actual named exact images of the given arrow. -/
theorem finiteScalarNormalizedClassRoute_eq (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT)
    (a : Etale.ordinaryFiniteUnit (FiniteRing l E n) T ⟶
      (Etale.ordinaryFiniteLine (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) T)⟦(2 : ℤ)⟧) :
    @Eq (FiniteScalarBoundaryArrow l E n T)
      (finiteScalarNormalizedAbelianRoute l E n T c a)
      (finiteScalarNormalizedClassRoute l E n T c a) := by
  exact ordinaryFiniteClass_exact_image_prepost (FiniteRing l E n) T
    (Scheme.finiteEtaleTateLine T (l ^ (n + 1)) (FiniteRing l E n)
      (ULift.ext (coefficient_annihilates l E n)))
    (comparisonUpperStar AddCommGrpCat.{u + 1} T) a
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map (integerComparison T).inv)
    (((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
      (finiteScalarLineCoordinate l E n T c))⟦(2 : ℤ)⟧')

end AlgebraicGeometry.ProEtale.DiagonalTrace
