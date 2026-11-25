module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Characterizing the ramification index

For an extension `B/A` of discrete valuation rings with ramification index `e = e(B/A)`:

* `e` is the only exponent `≥ 1` with `𝔪_A B = 𝔪_B ^ e`;
* for any uniformizers `π_A`, `π_B`, the image of `π_A` is a unit times `π_B ^ e`.

## Main results

* `IsDiscreteValuationRing.ramificationIndex_unique`: the exponent is unique.
* `IsDiscreteValuationRing.exists_unit_algebraMap_eq_mul_pow`: the uniformizer description.
* `IsDiscreteValuationRing.map_maximalIdeal_eq_iff_isWeaklyUnramified`: `B/A` is weakly
  unramified if and only if `𝔪_A B = 𝔪_B`.
* `IsDiscreteValuationRing.isWeaklyUnramified_iff_exists_unit_algebraMap_eq_mul`: `B/A` is weakly
  unramified if and only if the image of `π_A` is a unit times `π_B`.

## References

* [Stacks Project, Tag 09E4](https://stacks.math.columbia.edu/tag/09E4)
-/

open Stacks.DiscreteValuationRing.Ramification

@[expose] public section

namespace IsDiscreteValuationRing

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [IsExtension A B]

/-- `B/A` is weakly unramified if and only if the maximal ideal of `A` extends to the maximal
ideal of `B`. -/
theorem map_maximalIdeal_eq_iff_isWeaklyUnramified :
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B ↔
      IsWeaklyUnramified A B := by
  obtain ⟨-, hpow, hunique, -⟩ := ramificationIndex_characterization A B
  refine ⟨fun h => (hunique 1 le_rfl (by simpa using h)).symm, fun h => ?_⟩
  change ramificationIndex A B = 1 at h
  simpa [h] using hpow

end IsDiscreteValuationRing
