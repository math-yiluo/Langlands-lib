/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryCompositeCoordinateArrow
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinarySingleComparison

/-! # Single comparison in the ordinary coefficient presentation

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-ordinary-coordinate-via-single).
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

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance 100001] finiteOrdinaryDerived finiteOrdinaryExt
  finiteOrdinaryIntrinsicDerived
attribute [local instance 100000] Etale.ordinaryFiniteDerivedCategoryInstance

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
  Functor.mapDerivedCategory Ext.homEquiv HasDerivedCategory.standard
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
  HomologicalComplex.quasiIso
attribute [local implicit_reducible] SpTowerShriek.tau spCoefficientCommRings
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  Etale.ordinaryFiniteDegreeZero Etale.ordinaryFiniteSingleFunctor
  diagonalAbSheafAbelian towerAbelian systemsAbelian

attribute [local instance 100000] CategoryTheory.Abelian.toPreadditive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The normalized image of an arbitrary single arrow under the actual
comparison-realization composite is successive exact single-arrow transport.
Source: exact functor composition and the single comparison isomorphisms
(blueprint: lem-sfb-finite-ordinary-coordinate-via-single).

Proof: apply coordinate_composite to the cached actual comparison and realization
functors, with arbitrary endpoint isomorphisms. The two single comparison
identities are finiteOrdinarySingleComparison_eq. Unfold the actual comparison
and composite functor to identify the normalized left side. -/
theorem finiteOrdinaryCoordinateArrow_via_single (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] (T : Scheme.{u})
    {M N : OrdinaryEtaleModules (FiniteRing l E n) T}
    {M' N' : Scheme.reductionModules T (SpTowerShriek.B l E T n)}
    (u : (finiteOrdinaryRealization l E n T).obj
      ((finiteOrdinaryComparison (FiniteRing l E n) T).obj M) ≅ M')
    (v : (finiteOrdinaryRealization l E n T).obj
      ((finiteOrdinaryComparison (FiniteRing l E n) T).obj N) ≅ N')
    (a : (DerivedCategory.singleFunctor (OrdinaryEtaleModules (FiniteRing l E n) T)
        0).obj M ⟶
      ((DerivedCategory.singleFunctor (OrdinaryEtaleModules (FiniteRing l E n) T)
        0).obj N)⟦(2 : ℤ)⟧) :
    @Eq (FiniteOrdinaryCoordinateArrowHom l E n T M' N')
      (finiteOrdinaryCompositeCoordinateArrow l E n T u v a)
      (finiteOrdinarySuccessiveCoordinateArrow l E n T u v a) := by
  exact coordinate_composite
    (C := OrdinaryEtaleModules (FiniteRing l E n) T)
    (D := OrdinaryProEtaleModules (FiniteRing l E n) T)
    (H := Scheme.reductionModules T (SpTowerShriek.B l E T n))
    (finiteOrdinaryComparison (FiniteRing l E n) T)
    (finiteOrdinaryRealization l E n T)
    (SpTowerP1.nuSingle l E n T M) (SpTowerP1.nuSingle l E n T N)
    (finiteOrdinarySingleComparison_eq l E n T M)
    (finiteOrdinarySingleComparison_eq l E n T N) u v 2 a

end AlgebraicGeometry.ProEtale.DiagonalTrace
