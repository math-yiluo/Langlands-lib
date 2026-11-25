/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerNormalized
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstruction
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoos
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Exact completed-coefficient tower functors and their Roos presentation

Source: latest blueprint, chap-Smooth-purity, sk-lem-sp-tower-equivalence.proof.md,
Adjunction paragraph; Stacks 0941 (blueprint: lem-sp-completed-tower-roos).

The five completed-tower constructions are moved verbatim from
SmoothPurityNormalizedEquivalence. Evaluation proves exactness of scalar forgetting.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Forget the finite-level actions to completed coefficients, retaining all strict
transitions. Source: blueprint, definition of L_T (blueprint:
lemma-sp-tower-adjunction-foundation). -/
def spCompletedStrictTower (D : SpCoefficientTowersAbelian l E T) :
    spCoefficientTowers l E T ⥤
      (ℕᵒᵖ ⥤ WeilConjectures.scalarReductionSource.{u, u} l E T) :=
  (Functor.ofOpSequence (spCompletedTransition l E T D)).flip

/-- The coefficient-ring identification transports the existing reduction functor
from section modules to modules over the completed ring. Source: blueprint, r_T
(blueprint: lemma-sp-tower-adjunction-foundation). -/
def spCompletedReduction (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :
    DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T) ⥤
      spDerivedCoefficientTowers l E T D :=
  (restrictScalars.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      R.coefficient.hom)).mapDerivedCategory ⋙ R.red

/-- Total derived inverse limit after the exact scalar-forgetting functor. The
fixed-ring limit is the existing K-injective total derived inverse limit, including its
resolution-normalized projections. Source: blueprint, L_T; Stacks 0941
(blueprint: lemma-sp-tower-adjunction-foundation). -/
def spCompletedTotalLimit (D : SpCoefficientTowersAbelian l E T)
    [(spCompletedStrictTower l E T D).Additive]
    [PreservesFiniteLimits (spCompletedStrictTower l E T D)]
    [PreservesFiniteColimits (spCompletedStrictTower l E T D)] :
    spDerivedCoefficientTowers l E T D ⥤
      DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T) :=
  letI := D.hasDerived
  (spCompletedStrictTower l E T D).mapDerivedCategory ⋙
    WeilConjectures.coefficientConstantTowerLimit l E T

/-- Exact evaluation commutes with forgetting the finite-level coefficient actions.
The comparison is the canonical localization comparison for the two exact composites.
Source: blueprint, definition of L_T (blueprint: lemma-sp-tower-adjunction-foundation). -/
def spCompletedForgettingEvaluationIso (D : SpCoefficientTowersAbelian l E T)
    [(spCompletedStrictTower l E T D).Additive]
    [PreservesFiniteLimits (spCompletedStrictTower l E T D)]
    [PreservesFiniteColimits (spCompletedStrictTower l E T D)] (n : ℕ) :
    @Functor.mapDerivedCategory _ _ _ D.hasDerived _ _ _
        (HasDerivedCategory.standard _) (spCompletedStrictTower l E T D) _ _ _ ⋙
      WeilConjectures.coefficientConstantTowerEvaluation l E T n ≅
        spDerivedCompletedEvaluation l E T D n :=
  letI := D.hasDerived
  letI := D.evaluationLimits n
  letI := D.evaluationColimits n
  letI : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
  Functor.mapDerivedCategoryCompIso (spCompletedStrictTower l E T D)
    ((evaluation ℕᵒᵖ (WeilConjectures.scalarReductionSource l E T)).obj (op n)) ≪≫
    (Functor.mapDerivedCategoryCompIso (spCoefficientEvaluation l E T D.equivalence n)
      (spCompletedEllRestriction l E T n)).symm

/-- The actual total-limit projection to each completed-coefficient level. Its
normalization comes from the existing projection on simultaneous K-injective towers.
Source: blueprint, total limit and its counit (blueprint: lemma-sp-tower-adjunction-foundation). -/
def spCompletedTotalProjection (D : SpCoefficientTowersAbelian l E T)
    [(spCompletedStrictTower l E T D).Additive]
    [PreservesFiniteLimits (spCompletedStrictTower l E T D)]
    [PreservesFiniteColimits (spCompletedStrictTower l E T D)] (n : ℕ) :
    spCompletedTotalLimit l E T D ⟶ spDerivedCompletedEvaluation l E T D n :=
  letI := D.hasDerived
  Functor.whiskerLeft (spCompletedStrictTower l E T D).mapDerivedCategory
    (WeilConjectures.coefficientConstantTowerProjection l E T n) ≫
      (spCompletedForgettingEvaluationIso l E T D n).hom

end AlgebraicGeometry.ProEtale
