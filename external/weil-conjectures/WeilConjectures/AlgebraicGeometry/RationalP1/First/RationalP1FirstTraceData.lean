/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1DiagonalTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange

/-! # The opposite exchange for the first projective-line trace
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

attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] condensedAmbientPullbackComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})

/-- The opposite mate of the fixed self-square comparison, followed by the specified
line comparison. It transports the q direct image of T to the first direct image of N. -/
@[irreducible]
def firstTraceExchange
    (T : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (e : (moduleObjectDerivedPullback Λ (secondProjection Y)).obj T ≅ N) :
    (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj
      ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).obj T) ⟶
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).obj N := by
  unfold moduleObjectDerivedPullback at e ⊢
  unfold moduleObjectDerivedPushforward
  exact (mateEquiv (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y))
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (firstProjection Y))
    (TwoSquare.mk _ _ _ _ (condensedAmbientPullbackComparison Λ (square Y)).inv)).app
      T ≫ (CondensedRing.lowerStar Λ (firstProjection Y)).rightDerivedFunctor.map e.hom

end AlgebraicGeometry.ProEtale.RationalP1
