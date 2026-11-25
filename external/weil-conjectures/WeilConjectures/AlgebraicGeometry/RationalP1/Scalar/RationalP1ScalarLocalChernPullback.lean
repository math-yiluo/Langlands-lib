/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernLocalFactorization

/-! # Pullback of the local scalar Chern classes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

/-- Pulling the local section class along p1 gives the section class of p2.
This is an equation of local classes on the product; it has no direct images,
exchange mate, completed Chern adjuncts, traces, or splitting maps. -/
theorem scalar_local_chern_pullback
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (r : Reference l Y δ family)
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧)
    (hz : CompletedLocalChernNormalized l r.tq.toPresentation z)
    (w : DiagonalTrace.completedUnit l (diagonalSurface Y) ⟶
      (DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧)
    (hw : CompletedLocalChernNormalized l r.t₂.toPresentation w) :
    let Λ := (coefficient l (some E)).X
    (ambientPullbackComparison Λ (square Y)).hom.app (unit Λ Y) ≫
        (moduleObjectDerivedPullback Λ (firstProjection Y)).map
          ((scalarUnitPullIso Λ Y).hom ≫ scalarQLocalChern l E Y r z) ≫
        (firstLineComparisonForTrace l (some E) k p hpl Y).hom =
      (moduleObjectDerivedPullback Λ (secondProjection Y)).map
          (scalarUnitPullIso Λ Y).hom ≫
        (scalarP2UnitIso Λ Y).hom ≫ scalarP2LocalChern l E Y r w := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
