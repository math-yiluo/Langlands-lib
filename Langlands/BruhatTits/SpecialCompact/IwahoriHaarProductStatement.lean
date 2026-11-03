import Langlands.BruhatTits.SpecialCompact.SmallSubgroupPredicates
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-! # Haar characters from a simultaneous Iwahori basis -/

universe u

open MeasureTheory
open scoped NNReal

namespace Langlands.BruhatTits.SpecialCompact

/-- A continuous automorphism preserving the three factors of a simultaneous
normal compact-open Iwahori basis has the product of their Haar characters. -/
def IwahoriHaarProductStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (M U V P K0 : Subgroup G) (B : Set (Subgroup G))
    (α : G ≃ₜ* G) (αM : M ≃ₜ* M) (αU : U ≃ₜ* U) (αV : V ≃ₜ* V)
    (hM : IsClosed (M : Set G)) (hU : IsClosed (U : Set G))
    (hV : IsClosed (V : Set G)),
    CompactOpenNormalBasis K0 B →
    (∀ K ∈ B, HasIwahoriIntersectionDecomposition K M U V) →
    M ≤ P → U ≤ P → Disjoint V P →
    (∀ m : M, α (m : G) = (αM m : G)) →
    (∀ x : U, α (x : G) = (αU x : G)) →
    (∀ x : V, α (x : G) = (αV x : G)) →
    haveI : LocallyCompactSpace M := hM.locallyCompactSpace
    haveI : LocallyCompactSpace U := hU.locallyCompactSpace
    haveI : LocallyCompactSpace V := hV.locallyCompactSpace
    mulEquivHaarChar α =
      mulEquivHaarChar αV * mulEquivHaarChar αM * mulEquivHaarChar αU

end Langlands.BruhatTits.SpecialCompact
