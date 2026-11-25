/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryReducedPullSourceIso
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryReducedPullTargetProjectionIso
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryReducedPullTargetProjectionModelIso

/-! # Target transport for ordinary finite reduction

The target-side transport to the finite quotient model is isolated here.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ConstantCompletion

namespace CategoryTheory.ConstantCompletion

variable {C C' : Type u} [SmallCategory C] [SmallCategory C']
variable {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)

/-- The target finite reduction has a transport to the same finite quotient model as
the source reduction.  This is the target half of the common-quotient argument.
Source: Stacks Project, sites-modules.tex, Tags 03EK, 03EL and 093M.
Proof: use the second-site quotient identification, the projection equation for
`completedMap`, and normalized scalar associativity for the inverse-image algebra.
(auxiliary; not a blueprint node).
-/
theorem ordinaryReducedPull_targetIso
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    Nonempty ((pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) ⋙
        change (quotient J' A I n)) ≅
      (change (projection J A I n) ⋙
        pull F (constantMap F (A ⧸ I ^ (n + 1))))) := by
  obtain ⟨e₁⟩ := ordinaryReducedPull_targetQuotientIso F A I n
  obtain ⟨e₂⟩ := ordinaryReducedPull_targetProjectionIso F V adj A I n
  exact ⟨e₁ ≪≫ e₂⟩

end CategoryTheory.ConstantCompletion
