/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondExchangeProjectionNative

/-! # Forward exchange and projection on the projective-line self-square
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
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

/-- The forward exchange/projection square, before adding an outside Tate factor.
There is no inverse projection, twisted projection, or invertibility assumption. -/
theorem second_exchange_projection
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K : DerivedCategory (Modules (coefficient l c).X Y)) :
    let Λ := (coefficient l c).X
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    let R := moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)
    let T := ((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
      (line l c (ProjectiveLine Y))) ⟦(2 : ℤ)⟧
    F.map (projectionMap Λ (ProjectiveLine Y ↘ Y) K T) ≫
        F.map (R.map (tensorShiftIso Λ (ProjectiveLine Y)
          (line l c (ProjectiveLine Y)) (F.obj K)).hom) ≫
        secondPretraceExchangeMap Λ Y
          ((twist Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj (F.obj K)) =
      (secondTraceTensorIso Λ Y K (R.obj T)).inv ≫
        (F.obj K ◁ secondTraceExchange l c k p hpl Y) ≫
        secondExtractProjection l c k p hpl Y K := by
  simpa only [secondPretraceExchangeMap, nativeExchange] using
    second_exchange_projection_native l c k p hpl Y K

end AlgebraicGeometry.ProEtale.RationalP1
