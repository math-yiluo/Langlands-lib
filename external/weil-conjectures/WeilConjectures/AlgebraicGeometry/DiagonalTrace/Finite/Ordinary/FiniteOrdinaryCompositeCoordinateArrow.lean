/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryTransportImages

/-! # Composite and successive ordinary coordinate arrows

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: def-sfb-finite-ordinary-composite-coordinate-arrow).
(blueprint: def-sfb-finite-ordinary-successive-coordinate-arrow).
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

/-- Actual Hom between two arbitrary intrinsic coordinate endpoints.
Source: the existing intrinsic degree-zero and shift constructions
(blueprint: def-sfb-finite-ordinary-composite-coordinate-arrow). -/
def FiniteOrdinaryCoordinateArrowHom (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] (T : Scheme.{u})
    (M' N' : Scheme.reductionModules T (SpTowerShriek.B l E T n)) :=
  (DerivedCategory.singleFunctor _ 0).obj M' ⟶
    ((DerivedCategory.singleFunctor _ 0).obj N')⟦(2 : ℤ)⟧

/-- Normalize the actual comparison-realization image using its given single
comparison and arbitrary endpoint coordinates. Source: exact single and shift
comparison (blueprint: def-sfb-finite-ordinary-composite-coordinate-arrow). -/
def finiteOrdinaryCompositeCoordinateArrow (n : ℕ)
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
    FiniteOrdinaryCoordinateArrowHom l E n T M' N' :=
  (((DerivedCategory.singleFunctor _ 0).mapIso u).symm ≪≫
      (SpTowerP1.nuSingle l E n T M).symm).hom ≫
    (Scheme.sfIntrinsicModuleEquivalence T
      (SpTowerShriek.R l E n)).functor.mapDerivedCategory.map
        ((comparisonUpperStar (ModuleCat.{u + 1} (FiniteRing l E n)) T).mapDerivedCategory.map a) ≫
    (((SpTowerP1.nu l E n T).commShiftIso (2 : ℤ)).app _ ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso
        ((SpTowerP1.nuSingle l E n T N) ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso v)).hom

/-- The same coordinates applied to the actual successive exact image.
Source: exact comparison and realization in normalized coordinates
(blueprint: def-sfb-finite-ordinary-successive-coordinate-arrow). -/
def finiteOrdinarySuccessiveCoordinateArrow (n : ℕ)
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
    FiniteOrdinaryCoordinateArrowHom l E n T M' N' :=
  (DerivedCategory.singleFunctor _ 0).map u.inv ≫
    finiteOrdinaryIntrinsicImage l E n T a ≫
    ((DerivedCategory.singleFunctor _ 0).map v.hom)⟦(2 : ℤ)⟧'

end AlgebraicGeometry.ProEtale.DiagonalTrace
