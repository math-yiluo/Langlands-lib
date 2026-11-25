/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import all WeilConjectures.AlgebraicGeometry.RationalP1.DiagonalCompletedChernSplitting
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteIntegralEndpoint
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalFlatScalarEndpoint
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Closure.DiagonalClosureLineEndpoint

/-! # A one-sided q Chern splitting existence statement
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] derivedScalars Functor.mapDerivedCategory RestrictionSquare.mate

/-- The q Chern arrow admits a complementary shifted line component. -/
theorem scalar_q_chern_splitting_exists
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (r : Reference l Y δ family)
    (a : DiagonalTrace.completedUnit l Y ⟶
      r.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧))
    (ha : CompletedChernNormalized l r.tq.toPresentation a) :
    ∃ v : ((DerivedCategory.singleFunctor
        (Modules (coefficient l c).X Y) 0).obj (line l c Y)) ⟦(2 : ℤ)⟧ ⟶
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj
        (((DerivedCategory.singleFunctor
          (Modules (coefficient l c).X (ProjectiveLine Y)) 0).obj
          (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧),
      IsIso (biprod.desc v (scalarQChern l c Y r a)) := by
  have hcompleted := completed_chern_splitting l r.tq hY a ha
  have hz := realize_splitting l _ r.eP r.eY r.tq.Rc family.zl.Rq r.q_square a hcompleted
  have hi (E : PadicAlgCl.FiniteIntermediateField l) :=
    extend_splitting (integralMap l E) _ ((family.toIntegral E).units Y)
      (family.toIntegral E).lineP
      (Classical.choice (diagonalFinite_integralEndpoint l E Y hY)) family.zl.Rq
      (family.integral E).Rq (family.toIntegral E).q.square
      (family.toIntegral E).q.comparison_iso _ hz
  have hq (E : PadicAlgCl.FiniteIntermediateField l) := by
    let := residueInvertible l Y hY
    let b := padicIntegersRingObjToContinuousMapRingObj l E
    have hEndpoint := diagonal_flat_scalar_endpoint_iso b Y
      (spIntegralTwist Y l E) (integralLine_flat l Y E)
    let eY : Endpoint b (spIntegralTwist Y l E) (spRationalTwist Y l E)
        (rationalLineMap l E Y) :=
      { semilinear := ⟨Mod.extendUnit (coefficientMap b Y) _, rfl⟩
        iso := hEndpoint.exists.choose
        normalization := hEndpoint.exists.choose_spec }
    exact extend_splitting b _
      ((family.toRational E).units Y)
      (family.toRational E).lineP eY
      (family.integral E).Rq (family.rational E).Rq
      (family.toRational E).q.square (family.toRational E).q.comparison_iso _ (hi E)
  cases c
  case some E =>
    unfold scalarQChern
    dsimp only [coefficient, line]
    exact postcompose_splitting _ (hq E)
      ((eqToIso (family.rational E).q_canonical).app _)
  case none =>
    unfold scalarQChern
    dsimp only [coefficient, line]
    have hclosure := extend_splitting
      (Profinite.padicSubfieldRingObjToPadicAlgCl l (bottomField l)) _
      ((family.toClosure (bottomField l)).units Y)
      (family.toClosure (bottomField l)).lineP
      (Classical.choice (diagonalClosure_lineEndpoint l (bottomField l) Y hY))
      (family.rational (bottomField l)).Rq family.closure.Rq
      (family.toClosure (bottomField l)).q.square
      (family.toClosure (bottomField l)).q.comparison_iso _ (hq (bottomField l))
    exact postcompose_splitting _ hclosure
      ((eqToIso family.closure.q_canonical).app _)

end AlgebraicGeometry.ProEtale.RationalP1
