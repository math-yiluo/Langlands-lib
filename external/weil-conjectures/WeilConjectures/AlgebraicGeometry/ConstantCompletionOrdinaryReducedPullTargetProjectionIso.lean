/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryReducedPullSourceIso

/-! # Target projection transport for ordinary finite reduction

The coefficient-side finite comparison removes the target quotient restriction.
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

/-- The target quotient restriction is canonically the target projection change-of-scalars.
Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL.
Proof: whisker the finite coefficient comparison on the second site by the completed
inverse-image pullback functor.
(auxiliary; not a blueprint node).
-/
theorem ordinaryReducedPull_targetQuotientIso (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    Nonempty ((pull F (completedMap F A I) ⋙ res (coefficientMap J' A I) ⋙
        change (quotient J' A I n)) ≅
      (pull F (completedMap F A I) ⋙ change (projection J' A I n))) := by
  exact ⟨Functor.isoWhiskerLeft (pull F (completedMap F A I))
    (finiteComparison J' A I n)⟩

end CategoryTheory.ConstantCompletion
