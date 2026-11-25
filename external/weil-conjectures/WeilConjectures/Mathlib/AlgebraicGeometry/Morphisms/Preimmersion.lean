/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Cancelling a preimmersion on the right

`AlgebraicGeometry.IsPreimmersion.of_comp'`: if a composite `f ≫ g` is a preimmersion, so is
`f`. This strengthens `AlgebraicGeometry.IsPreimmersion.of_comp`, which additionally assumes
that `g` is a preimmersion.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If a composite `f ≫ g` is a preimmersion, so is its first factor `f`. -/
lemma IsPreimmersion.of_comp' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsPreimmersion (f ≫ g)] : IsPreimmersion f where
  toSurjectiveOnStalks := SurjectiveOnStalks.of_comp f g
  isEmbedding := Topology.IsEmbedding.of_comp f.continuous g.continuous (f ≫ g).isEmbedding

end AlgebraicGeometry
