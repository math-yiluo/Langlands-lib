/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedFiniteExchangeCoordinates
public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenScalars.FiniteOpenExchangeScalars
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange

/-!
# Representative models for the finite completed-ring comparisons

Source: Stacks 06YY, 099N and 06XN; finite-exchange proof Step 7
(blueprint: def-cbc-finite-comparison-models).

These model maps and normalization predicates retain exactly the original
finite scalar action and universal counit equations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)

open AlgebraicGeometry.ProEtale.StrictTower

/-- The finite reduction's universal comparison, retaining its own finite action.
Source: Stacks 06YY (blueprint: def-cbc-finite-comparison-models). -/
def cbcFiniteReductionModelMap (T : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    (cbcFiniteReduction d T n).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((cbcFiniteReductionModule d T n).mapHomologicalComplex (.up ℤ)).obj P) :=
  (pbcDerivedRestrict (pbcLevelConstantComparison T d n).hom).map
      (pbcComplexCounit (pbcAdicProjection T d n) P) ≫
    (pbcRestrict (pbcLevelConstantComparison T d n).hom).mapDerivedCategoryFactors.hom.app
      (((reductionChange T (pbcAdicProjection T d n)).mapHomologicalComplex (.up ℤ)).obj P)

/-- Finite source comparison on representatives.
Source: Stacks 06YY (blueprint: def-cbc-finite-comparison-models). -/
def cbcFiniteSourceModelMap (n : ℕ)
    (P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ) :
    (cbcFiniteReduction d U n ⋙ (cbcFiniteSource d sq n).mapDerivedCategory).obj
      (DerivedCategory.Q.obj P) ⟶
    DerivedCategory.Q.obj
      (((cbcFiniteSource d sq n).mapHomologicalComplex (.up ℤ)).obj
        (((cbcFiniteReductionModule d U n).mapHomologicalComplex (.up ℤ)).obj P)) :=
  (cbcFiniteSource d sq n).mapDerivedCategory.map (cbcFiniteReductionModelMap d U n P) ≫
    (cbcFiniteSource d sq n).mapDerivedCategoryFactors.hom.app
      (((cbcFiniteReductionModule d U n).mapHomologicalComplex (.up ℤ)).obj P)

/-- Finite target comparison on representatives.
Source: Stacks 06YY (blueprint: def-cbc-finite-comparison-models). -/
def cbcFiniteTargetModelMap (n : ℕ)
    (P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ) :
    (cbcFiniteReduction d U n ⋙ (cbcFiniteTarget d sq n).mapDerivedCategory).obj
      (DerivedCategory.Q.obj P) ⟶
    DerivedCategory.Q.obj
      (((cbcFiniteTarget d sq n).mapHomologicalComplex (.up ℤ)).obj
        (((cbcFiniteReductionModule d U n).mapHomologicalComplex (.up ℤ)).obj P)) :=
  (cbcFiniteTarget d sq n).mapDerivedCategory.map (cbcFiniteReductionModelMap d U n P) ≫
    (cbcFiniteTarget d sq n).mapDerivedCategoryFactors.hom.app
      (((cbcFiniteReductionModule d U n).mapHomologicalComplex (.up ℤ)).obj P)

/-- Normalization of the finite source comparison on every K-flat representative.
Source: Stacks 099N, 06XN (blueprint: def-cbc-finite-comparison-models). -/
def CbcSourceFiniteNormalization (n : ℕ)
    (e : completedReductionTower U d ⋙ cbcStrictOpen d j sq.isOpenImmersion ⋙
        completedTowerPullback g d ⋙ pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
      cbcFiniteReduction d U n ⋙ (cbcFiniteSource d sq n).mapDerivedCategory) : Prop :=
  ∀ P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P →
    HEq
      ((pbcTowerEvaluation X' (pbcAdicCompletion X' d) n).map (cbcSourceModelMap d sq P) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj
        (op n)).mapDerivedCategoryFactors.hom.app
          (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
            (((cbcStrictOpenModule d j sq.isOpenImmersion).mapHomologicalComplex (.up ℤ)).obj
              (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj
                P))) ≫
      DerivedCategory.Q.map ((@NatTrans.mapHomologicalComplex _ _ _ _ _ _ _ _ _
        (cbcSourceLevel_preservesZeroMorphisms d sq n)
        (cbcFiniteSourceModel_preservesZeroMorphisms d sq n)
        (cbcSourceLevel d sq n).hom (.up ℤ)).app P))
      (e.hom.app (DerivedCategory.Q.obj P) ≫ cbcFiniteSourceModelMap d sq n P)

/-- Normalization of the finite target comparison on the identical representative class.
Source: Stacks 099N, 06XN (blueprint: def-cbc-finite-comparison-models). -/
def CbcTargetFiniteNormalization (n : ℕ)
    (e : completedReductionTower U d ⋙ completedTowerPullback gU d ⋙
        cbcStrictOpen d j' sq.isOpenImmersion' ⋙
          pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
      cbcFiniteReduction d U n ⋙ (cbcFiniteTarget d sq n).mapDerivedCategory) : Prop :=
  ∀ P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P →
    HEq
      ((pbcTowerEvaluation X' (pbcAdicCompletion X' d) n).map (cbcTargetModelMap d sq P) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj
        (op n)).mapDerivedCategoryFactors.hom.app
          (((cbcStrictOpenModule d j' sq.isOpenImmersion').mapHomologicalComplex (.up ℤ)).obj
            (((completedTowerModulePullback gU d).mapHomologicalComplex (.up ℤ)).obj
              (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj
                P))) ≫
      DerivedCategory.Q.map ((@NatTrans.mapHomologicalComplex _ _ _ _ _ _ _ _ _
        (cbcTargetLevel_preservesZeroMorphisms d sq n)
        (cbcFiniteTargetModel_preservesZeroMorphisms d sq n)
        (cbcTargetLevel d sq n).hom (.up ℤ)).app P))
      (e.hom.app (DerivedCategory.Q.obj P) ≫ cbcFiniteTargetModelMap d sq n P)

end AlgebraicGeometry.Scheme
