/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPretraceData
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondProjectionInterchangeCore
import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondProjectionInterchangeTail

/-! # Interchanging a Tate factor with the second projection
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

/-- Move an outside shifted Tate factor across a forward two-factor projection.
This is a projection/tensor equation for an arbitrary scalar arrow z; it contains
no exchange map, unitTail, counitProjectionPart, or inverse projection. -/
theorem second_projection_interchange
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    (K V : DerivedCategory (Modules (coefficient l c).X Y))
    (z : (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj V ⟶
      (moduleObjectDerivedPushforward (coefficient l c).X (secondProjection Y)).obj
        (((DerivedCategory.singleFunctor (Modules (coefficient l c).X (diagonalSurface Y))
          0).obj (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧)) :
    let Λ := (coefficient l c).X
    let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
    let H := twist Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y))
    (secondTraceStrength Λ Y (line l c (ProjectiveLine Y)) K V).hom ≫
        H.map ((secondTraceTensorIso Λ Y K V).inv ≫
          (F.obj K ◁ z) ≫ secondExtractProjection l c k p hpl Y K) ≫
        twistProjectionMap Λ (secondProjection Y)
          (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
          (secondLineComparison l c k p hpl Y)
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj (H.obj (F.obj K))) =
      (H.obj (F.obj K) ◁ z) ≫ secondForwardProjection l c k p hpl Y K := by
  dsimp
  let Λ := (coefficient l c).X
  have h := (secondTraceStrength_naturality l c k p hpl Y K V
      ((moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        (((DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
          (line l c (diagonalSurface Y))) ⟦(2 : ℤ)⟧))
      ((moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj
          ((twist Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
            ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K))))
      ((moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((twist Λ (diagonalSurface Y) (line l c (diagonalSurface Y))).obj
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj
            ((twist Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
              ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K))))) z
      (secondExtractProjection l c k p hpl Y K)
      (twistProjectionMap Λ (secondProjection Y)
        (line l c (ProjectiveLine Y)) (line l c (diagonalSurface Y))
        (secondLineComparison l c k p hpl Y)
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj
          ((twist Λ (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
            ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K)))
  ))
  rw [h]
  exact congrArg (fun f ↦
    ((twist (coefficient l c).X (ProjectiveLine Y) (line l c (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K) ◁ z) ≫ f)
    (second_projection_tail_cancellation l c k p hpl Y K)

end AlgebraicGeometry.ProEtale.RationalP1
