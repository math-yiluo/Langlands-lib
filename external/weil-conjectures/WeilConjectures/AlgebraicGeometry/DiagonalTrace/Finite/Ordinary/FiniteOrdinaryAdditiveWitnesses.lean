/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryCoefficientModel

/-! # Scalar transport of an arbitrary finite ordinary arrow

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-ordinary-additive-witnesses).
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
attribute [local instance 100000] Etale.ordinaryFiniteDerivedCategoryInstance

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
attribute [local implicit_reducible] SpTowerShriek.tau spCoefficientCommRings
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  Etale.ordinaryFiniteDegreeZero Etale.ordinaryFiniteSingleFunctor
  diagonalAbSheafAbelian towerAbelian systemsAbelian

attribute [local instance 100000] CategoryTheory.Abelian.toPreadditive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Exact realization is additive with the inherited abelian preadditive structures.
Source: additivity of comparison and intrinsic realization
(blueprint: lem-sfb-finite-ordinary-additive-witnesses). -/
theorem finiteOrdinaryRealizationCompositeAdditive (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] (T : Scheme.{u}) :
    (finiteOrdinaryComparison (FiniteRing l E n) T ⋙
      finiteOrdinaryRealization l E n T).Additive := by
  constructor
  intro M N f g
  simp only [Functor.comp_map, Functor.map_add]

/-- Finite forgetting is additive with the inherited abelian preadditive structures.
Source: the underlying additive sheaf map
(blueprint: lem-sfb-finite-ordinary-additive-witnesses). -/
theorem finiteOrdinaryScalarForgetAdditive (T : Scheme.{u}) (n : ℕ) :
    (finiteForget l E T n).Additive := by
  constructor
  intro M N f g
  rfl

/-- The alternate ordinary scalar route is additive with those same structures.
Source: module-to-abelian forgetting and exact abelian comparison
(blueprint: lem-sfb-finite-ordinary-additive-witnesses). -/
theorem finiteOrdinaryAbelianCompositeAdditive (T : Scheme.{u}) (n : ℕ) :
    (Etale.moduleAbelianForget (FiniteRing l E n) T ⋙
      comparisonUpperStar AddCommGrpCat.{u + 1} T).Additive := by
  constructor
  intro M N f g
  simp only [Functor.comp_map, Functor.map_add]

end AlgebraicGeometry.ProEtale.DiagonalTrace
