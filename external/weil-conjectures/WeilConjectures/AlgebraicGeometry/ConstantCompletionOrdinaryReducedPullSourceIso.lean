/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryFinitePull

/-! # Source transport for ordinary finite reduction

This is the source-side transport used in the ordinary reduced pull comparison.
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

/-- The source finite reduction has its canonical transport to the finite quotient model.
Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL.
Proof: whisker the normalized ordinary finite pullback isomorphism on the left by
restriction of scalars, then whisker the normalized finite comparison on the right.
(auxiliary; not a blueprint node).
-/
theorem ordinaryReducedPull_sourceIso
    (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteLimits L] (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    Nonempty ((res (coefficientMap J A I) ⋙ pull F (constantMap F A) ⋙
        change (quotient J' A I n)) ≅
      (change (projection J A I n) ⋙
        pull F (constantMap F (A ⧸ I ^ (n + 1))))) := by
  obtain ⟨e, _⟩ := (ordinaryFinitePull_existsUnique F V adj A I n).exists
  exact ⟨Functor.isoWhiskerLeft (res (coefficientMap J A I)) e ≪≫
    Functor.isoWhiskerRight (finiteComparison J A I n)
      (pull F (constantMap F (A ⧸ I ^ (n + 1))))⟩

end CategoryTheory.ConstantCompletion
