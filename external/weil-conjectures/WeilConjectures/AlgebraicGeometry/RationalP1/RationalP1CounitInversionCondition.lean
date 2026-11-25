/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Ambient.RationalP1AmbientComposites

/-! # Cached rational projective-line inversion conditions -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Exactly the projection inversion witness needed by the trace counit formula.
The source and target derived-category instances are cached in this definition. -/
def CounitInversionCondition (Y : Scheme.{u}) (L : ∀ X : Scheme.{u}, Modules Λ X)
    (K : DerivedCategory (Modules Λ Y)) : Prop :=
  IsIso (projectionMap Λ (ProjectiveLine Y ↘ Y) K
    (((DerivedCategory.singleFunctor (Modules Λ (ProjectiveLine Y)) 0).obj
      (L (ProjectiveLine Y))) ⟦(2 : ℤ)⟧))

end AlgebraicGeometry.ProEtale.RationalP1
