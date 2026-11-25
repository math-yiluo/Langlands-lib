/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Scalar.FiniteScalarTransportRoutes
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryAdditiveWitnesses

/-! # Scalar transport of an arbitrary finite ordinary arrow

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-coefficient-transport-comparison).
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
open SpTowerClasses SpTowerClasses.FiniteExactArrow
attribute [local instance 100000] CategoryTheory.Abelian.toPreadditive

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance 100002] finiteOrdinaryRealizationCompositeAdditive
  finiteOrdinaryScalarForgetAdditive finiteOrdinaryAbelianCompositeAdditive
attribute [local instance 100001] finiteOrdinaryDerived finiteOrdinaryExt
  finiteOrdinaryIntrinsicDerived
attribute [local instance 100000] Etale.ordinaryFiniteDerivedCategoryInstance

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
attribute [local implicit_reducible] SpTowerShriek.tau spCoefficientCommRings
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  Etale.ordinaryFiniteDegreeZero Etale.ordinaryFiniteSingleFunctor
  diagonalAbSheafAbelian towerAbelian systemsAbelian

attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  HomologicalComplex.quasiIso DerivedCategory.singleFunctors
  finiteScalarComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The comparison of the two successive exact scalar transports before endpoint
normalization. Source: exact comparison and the realization unit
(blueprint: lem-sfb-finite-coefficient-transport-comparison). -/
theorem finiteOrdinaryScalarTransportComparison (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] (T : Scheme.{u})
    {M N : OrdinaryEtaleModules (FiniteRing l E n) T}
    (a : (DerivedCategory.singleFunctor (OrdinaryEtaleModules (FiniteRing l E n) T)
        0).obj M ⟶
      ((DerivedCategory.singleFunctor (OrdinaryEtaleModules (FiniteRing l E n) T)
        0).obj N)⟦(2 : ℤ)⟧) :
    @Eq (FiniteOrdinaryScalarArrow l E n T M N)
      (finiteScalarModuleRoute l E n T a)
      (finiteScalarAbelianRoute l E n T a) := by
  exact mapSingleArrow_three_comp_iso_arrow
    (C := OrdinaryEtaleModules (FiniteRing l E n) T)
    (D := OrdinaryProEtaleModules (FiniteRing l E n) T)
    (H := Scheme.reductionModules T (SpTowerShriek.B l E T n))
    (I := Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (B := DiagonalAb T)
    (finiteOrdinaryComparison (FiniteRing l E n) T)
    (finiteOrdinaryRealization l E n T) (finiteForget l E T n)
    (Etale.moduleAbelianForget (FiniteRing l E n) T)
    (comparisonUpperStar AddCommGrpCat.{u + 1} T)
    (finiteScalarCompositeComparison l E n T) 2 a

end AlgebraicGeometry.ProEtale.DiagonalTrace
