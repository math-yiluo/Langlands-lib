/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Scalar.FiniteScalarCoordinateRoutes
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Coefficient.FiniteCoefficientTransportComparison
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Scalar.FiniteScalarCoordinateNormalization

/-! # Scalar transport of an arbitrary finite ordinary arrow

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-coefficient-coordinate-conjugation).
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

/-- Exact scalar conjugation in coefficient coordinates, before realizing an
ordinary cohomology class. Source: diagonal-tower trace (1), exact forgetting
(blueprint: lem-sfb-finite-coefficient-coordinate-conjugation).

Proof: apply exact scalar conjugation to comparison, realization and forgetting.
The unit-section normalization is the source equation, so its inverse cancels.
The target comparison is the cached scalar line coordinate. All substitutions
are made in the generic category calculation before specialization. -/
theorem finiteOrdinaryCoordinateArrow_scalar_expanded (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT)
    (a : Etale.ordinaryFiniteUnit (FiniteRing l E n) T ⟶
      (Etale.ordinaryFiniteLine (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) T)⟦(2 : ℤ)⟧) :
    @Eq (FiniteScalarBoundaryArrow l E n T)
      (finiteScalarNormalizedModuleRoute l E n T c a)
      (finiteScalarNormalizedAbelianRoute l E n T c a) := by
  exact finiteScalarCoordinate_normalization l E n T c
    (finiteOrdinaryLineCoordinate l E n T c) ((finiteScalarComparison l E n T).app _)
    (finiteScalarLineCoordinate l E n T c) (finiteScalarLineCoordinate_eq l E n T c)
    (finiteOrdinaryIntrinsicImage l E n T a) (finiteOrdinaryAbelianImage l E n T a)
    (finiteOrdinaryScalarTransportComparison l E n T a)

end AlgebraicGeometry.ProEtale.DiagonalTrace
