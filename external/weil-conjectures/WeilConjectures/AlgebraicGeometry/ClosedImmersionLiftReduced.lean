/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!

# Lifting morphisms from reduced schemes through closed immersions

A morphism `g : Y ⟶ Z` from a reduced scheme whose image lies in the image of a closed immersion
`f : X ⟶ Z` factors through `f` (`AlgebraicGeometry.ker_le_ker_of_isReduced`, to be used with
`AlgebraicGeometry.IsClosedImmersion.lift`): the kernel of `g` is the vanishing ideal of the
closure of its image, which contains the kernel of `f`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

/-- A morphism from a reduced scheme with image inside the image of a closed immersion `f` has
kernel containing that of `f`. -/
theorem ker_le_ker_of_isReduced {X Y Z : Scheme.{u}} (f : X ⟶ Z) [IsClosedImmersion f]
    (g : Y ⟶ Z) [IsReduced Y] (h : Set.range g.base ⊆ Set.range f.base) : f.ker ≤ g.ker := by
  have hg : g.ker = IdealSheafData.vanishingIdeal (.closure (g.base '' Set.univ)) := by
    rw [← IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot,
      ← IdealSheafData.vanishingIdeal_top, IdealSheafData.map_vanishingIdeal]
    rfl
  rw [hg, ← IdealSheafData.le_support_iff_le_vanishingIdeal]
  intro z hz
  rw [← SetLike.mem_coe, Hom.support_ker]
  exact closure_mono (by rwa [Set.image_univ]) hz

end AlgebraicGeometry
