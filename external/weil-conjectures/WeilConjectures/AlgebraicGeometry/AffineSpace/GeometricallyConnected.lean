/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# The affine line over a field is geometrically connected

The affine line `𝔸¹_k` over a field `k` is irreducible, hence connected, and has the `k`-rational
point `0`; a connected `k`-scheme with a `k`-rational point is geometrically connected.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The affine line over a field is geometrically connected. -/
instance affineLine.geometricallyConnected (k : Type u) [Field k] :
    GeometricallyConnected (affineLine k ↘ Spec (CommRingCat.of k)) :=
  GeometricallyConnected.of_connectedSpace_of_section _
    (AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of k))) 0)
    (AffineSpace.homOfVector_over _ _)

end AlgebraicGeometry
