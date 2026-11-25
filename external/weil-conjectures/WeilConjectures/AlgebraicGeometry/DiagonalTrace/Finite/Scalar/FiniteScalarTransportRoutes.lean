/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Coefficient.FiniteCoefficientScalarComparison
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryAdditiveWitnesses
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryTransportImages

/-! # The actual two finite scalar transport routes

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: def-sfb-finite-scalar-transport-routes).
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

/-- Successive comparison, realization and coefficient forgetting of the given arrow.
Source: the three actual exact functors
(blueprint: def-sfb-finite-scalar-transport-routes). -/
def finiteScalarModuleRoute (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] (T : Scheme.{u})
    {M N : OrdinaryEtaleModules (FiniteRing l E n) T}
    (a : (DerivedCategory.singleFunctor (OrdinaryEtaleModules (FiniteRing l E n) T)
        0).obj M ⟶
      ((DerivedCategory.singleFunctor (OrdinaryEtaleModules (FiniteRing l E n) T)
        0).obj N)⟦(2 : ℤ)⟧) : FiniteOrdinaryScalarArrow l E n T M N :=
  mapSingleArrow (finiteForget l E T n) (2 : ℤ)
        (finiteOrdinaryIntrinsicImage l E n T a)

/-- Ordinary module forgetting and abelian comparison, with the actual scalar
comparison isomorphisms at the endpoints. Source: exact site comparison
(blueprint: def-sfb-finite-scalar-transport-routes). -/
def finiteScalarAbelianRoute (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] (T : Scheme.{u})
    {M N : OrdinaryEtaleModules (FiniteRing l E n) T}
    (a : (DerivedCategory.singleFunctor (OrdinaryEtaleModules (FiniteRing l E n) T)
        0).obj M ⟶
      ((DerivedCategory.singleFunctor (OrdinaryEtaleModules (FiniteRing l E n) T)
        0).obj N)⟦(2 : ℤ)⟧) : FiniteOrdinaryScalarArrow l E n T M N :=
  (DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          ((finiteScalarComparison l E n T).inv.app
            M) ≫
        finiteOrdinaryAbelianImage l E n T a ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          ((finiteScalarComparison l E n T).hom.app
            N))⟦(2 : ℤ)⟧'

end AlgebraicGeometry.ProEtale.DiagonalTrace
