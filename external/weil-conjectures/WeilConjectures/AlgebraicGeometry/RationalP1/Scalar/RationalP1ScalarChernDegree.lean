/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernQDegree
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernP2Degree

/-! # Trace one on the two transported Chern generators
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] singleUnitIso
attribute [local irreducible] moduleObjectDerivedPullback
attribute [local irreducible] firstProjection secondProjection square derivedScalars
attribute [local irreducible] Functor.mapDerivedCategory RestrictionSquare.mate
attribute [local irreducible] CompletedRealization.singleUnit CompletedRealization.shiftedLine

/-- Each independently transported Chern adjunct has trace one. -/
theorem scalar_chern_degree
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
    (ha : CompletedChernNormalized l r.tq.toPresentation a)
    (b : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      r.t₂.Rc.R.obj ((DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧))
    (hb : CompletedChernNormalized l r.t₂.toPresentation b) :
    let Λ := (coefficient l c).X
    let d := diagram l c Y family
    scalarQChern l c Y r a ≫ trace Λ Y (line l c) d = 𝟙 _ ∧
      scalarP2Chern l c Y r b ≫
        (secondDiagramPushIso Λ Y (line l c) d).inv.app
          (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
            (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧) ≫ d.trace₂ = 𝟙 _ := by
  exact ⟨scalar_chern_q_degree l c Y hY δ family r a ha,
    scalar_chern_p2_degree l c Y hY δ family r b hb⟩

end AlgebraicGeometry.ProEtale.RationalP1
