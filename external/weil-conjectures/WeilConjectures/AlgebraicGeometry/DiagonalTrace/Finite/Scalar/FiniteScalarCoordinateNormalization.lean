/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Scalar.FiniteScalarCoordinateRoutes
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Coefficient.FiniteCoefficientUnitCoordinate
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus

/-! # Scalar transport of an arbitrary finite ordinary arrow

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-scalar-coordinate-normalization).
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

/-- Source and target normalizations conjugate any pair of related scalar arrows.
Source: exact single-arrow endpoint naturality and the given unit section equation
(blueprint: lem-sfb-finite-scalar-coordinate-normalization).

Proof: apply coordinate_transport_of_comparison to the fixed finite forgetful
functor and the given coefficient coordinates. The source equation is
finiteScalarUnitCoordinate. The arbitrary target map is specified by hr, and
the arbitrary middle arrows are related by the cached comparison relation hd. -/
theorem finiteScalarCoordinate_normalization (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT)
    {Y Y' : Scheme.reductionModules T (SpTowerShriek.B l E T n)}
    {Y₀ : DiagonalAb T} (v : Y ≅ Y') (β : Y₀ ≅ (finiteForget l E T n).obj Y)
    (r : Y₀ ⟶ (finiteForget l E T n).obj Y')
    (hr : r = β.hom ≫ (finiteForget l E T n).map v.hom)
    (a : FiniteScalarIntrinsicArrow l E n T Y)
    (d : FiniteScalarAbelianArrow l E n T Y₀)
    (hd : FiniteScalarTransportRelation l E n T a d β) :
    @Eq (FiniteScalarIntegralArrow n T ((finiteForget l E T n).obj Y'))
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map (finiteQuotient l E T n) ≫
        mapSingleArrow (finiteForget l E T n) (2 : ℤ)
          ((DerivedCategory.singleFunctor _ 0).map
              (finiteOrdinaryUnitCoordinate l E n T c).inv ≫ a ≫
            ((DerivedCategory.singleFunctor _ 0).map v.hom)⟦(2 : ℤ)⟧'))
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map (integerComparison T).inv ≫
        (DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          ((comparisonUpperStar AddCommGrpCat.{u + 1} T).map
            (Etale.ordinaryFiniteIntegralGenerator (FiniteRing l E n) T)) ≫ d ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map r)⟦(2 : ℤ)⟧') := by
  exact coordinate_transport_of_comparison
    (H := Scheme.reductionModules T (SpTowerShriek.B l E T n))
    (B := DiagonalAb T) (finiteForget l E T n)
    (finiteOrdinaryUnitCoordinate l E n T c) v
    ((finiteScalarComparison l E n T).app _) β
    (finiteQuotient l E T n) (integerComparison T).inv
    ((comparisonUpperStar AddCommGrpCat.{u + 1} T).map
      (Etale.ordinaryFiniteIntegralGenerator (FiniteRing l E n) T))
    (finiteScalarUnitCoordinate l E n T c) (2 : ℤ) a d hd _ rfl r hr

end AlgebraicGeometry.ProEtale.DiagonalTrace
