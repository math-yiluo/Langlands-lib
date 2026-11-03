import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.Topology.LocallyConstant.Basic

/-! # Regularity of the modular character of a nonarchimedean group -/

namespace Langlands.Haar

open MeasureTheory.Measure

universe u

/-- Mathlib's modular character has open kernel, is locally constant and
continuous, and is trivial on every compact subgroup of a locally compact
nonarchimedean group. No second-countability premise is needed. -/
def ModularCharacterRegularityStatement : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [LocallyCompactSpace G],
    IsOpen ((modularCharacter (G := G)).ker : Set G) ∧
      IsLocallyConstant (modularCharacter (G := G)) ∧
      Continuous (modularCharacter (G := G)) ∧
      ∀ (K : Subgroup G), IsCompact (K : Set G) →
        ∀ g ∈ K, modularCharacter g = 1

end Langlands.Haar
