/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smoothness of the affine line

The affine line `𝔸¹_R ⟶ Spec R` over a commutative ring `R` is smooth of relative dimension one
(`AlgebraicGeometry.affineLine.smoothOfRelativeDimension_one`).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- The affine line `𝔸¹_R ⟶ Spec R` is smooth of relative dimension one. -/
instance affineLine.smoothOfRelativeDimension_one (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (affineLine R ↘ Spec (.of R)) := by
  simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of R))

end AlgebraicGeometry
