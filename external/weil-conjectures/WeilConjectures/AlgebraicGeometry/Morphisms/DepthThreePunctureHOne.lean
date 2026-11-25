/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthThreeLocalCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedHOneLocalCohomologyComparison

/-! # First cohomology of the structure sheaf on a depth-three puncture

## References

* Stacks Project, Tag 0BK0 (Lemma 51.8.2) and Tag 0AVY (Lemma 47.11.1)
-/

@[expose] public section

universe u
namespace AlgebraicGeometry.Scheme

/-- The first structure-sheaf cohomology of a depth-three puncture vanishes. -/
theorem depth_three_puncture_h_one
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    Subsingleton (Modules.H (X := W.toScheme)
      (SheafOfModules.unit W.toScheme.ringCatSheaf) 1) := by
  apply punctured_h_one_subsingleton_of_local_cohomology_vanishing R W hW
  exact depth_three_local_cohomology_vanishing R hdepth

end AlgebraicGeometry.Scheme
