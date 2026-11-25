/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondProjectionInterchangeCore
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondProjectionTailCore

/-! Cancellation of the fixed Tate projection tail. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line twist projectionMap tensorShiftIso
attribute [local irreducible] secondLineComparison twistProjectionMap
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square condensedAmbientExchange

/-- The fixed projection tail obtained after the strength naturality step is
exactly the forward second projection. It is independent of the outside arrow. -/
theorem second_projection_tail_cancellation
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    let Λ := (coefficient l c).X
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    let H := twist Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y))
    let Q := (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
        (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)
    let R := (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj (H.obj (F.obj K)))
    let Z := (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      ((twist Λ (diagonalSurface Y) (line l c (diagonalSurface Y))).obj
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj (H.obj (F.obj K))))
    secondTraceStrengthTail Λ Y (line l c (ProjectiveLine Y)) K Q ≫
        H.map (secondExtractProjection l c k p hpl Y K) ≫
        twistProjectionMap Λ (secondProjection Y)
          (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
          (secondLineComparison l c k p hpl Y)
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj (H.obj (F.obj K))) =
      secondForwardProjection l c k p hpl Y K := by
  dsimp
  simpa only [secondForwardProjection] using
    (second_projection_tail_cancellation_expanded l c k p hpl Y K)

end AlgebraicGeometry.ProEtale.RationalP1
