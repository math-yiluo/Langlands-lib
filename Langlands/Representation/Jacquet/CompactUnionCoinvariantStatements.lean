import Langlands.Representation.Jacquet.Coinvariants
import Langlands.Representation.Hecke.ActionProjection
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.HarmonicAnalysis.GroupAction

/-!
# Coinvariants: the Haar example and groups that are unions of compact subgroups
(Renard III.2.9)

The left-regular coinvariants of `𝒟(G)` are one-dimensional. If a t.d. group `H` is the
filtered increasing union of its compact subgroups, every compact subset lies in a compact
subgroup, the coinvariant relations of a smooth representation are the vectors killed by the
average `τ(e_K)` over some compact subgroup `K`, and the relations of a subrepresentation are
its intersection with the relations of the whole representation.
-/

namespace Langlands.Jacquet

open MeasureTheory

universe uH uV

/-- Renard III.2.9, Example: for a t.d. group `G`, the coinvariants `𝒟(G)_{G,l}` of the
left regular representation on test functions have dimension `1`. -/
def HaarCoinvariantsDimensionStatement : Prop :=
  ∀ (G : Type uH) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G],
    Module.finrank ℂ (Coinvariants (HarmonicAnalysis.GroupAction.leftTests (G := G)) ⊤) = 1

/-- Renard III.2.9, Remark after the Definition: if the t.d. group `H` is the filtered
increasing union of its compact subgroups (their union is `H`, and every finite family of them
is contained in one of them), then every compact subset of `H` lies in a compact subgroup. -/
def CompactSubgroupFilteredUnionStatement : Prop :=
  ∀ (H : Type uH) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [TotallyDisconnectedSpace H],
    (⋃ K : {K : Subgroup H // IsCompact (K : Set H)}, (K.1 : Set H)) = Set.univ →
    (∀ s : Finset {K : Subgroup H // IsCompact (K : Set H)},
      ∃ L : {K : Subgroup H // IsCompact (K : Set H)},
        (⋃ K ∈ s, (K.1 : Set H)) ⊆ (L.1 : Set H)) →
    ∀ C : Set H, IsCompact C → ∃ K : Subgroup H, IsCompact (K : Set H) ∧ C ⊆ K

/-- Renard III.2.9, Proposition: if the t.d. group `H` is the filtered increasing union of its
compact subgroups and `τ` is smooth, then `v` lies in `E(H, τ)` if and only if
`τ(e_K) · v = 0` for some compact subgroup `K`, where `τ(e_K)` is the action of the normalized
Haar measure of `K` (the published `fixedProjection` of the compact group `K`, for any Haar
measure on `K`). -/
def CompactAveragingRelationStatement : Prop :=
  ∀ (H : Type uH) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [TotallyDisconnectedSpace H],
    (⋃ K : {K : Subgroup H // IsCompact (K : Set H)}, (K.1 : Set H)) = Set.univ →
    (∀ s : Finset {K : Subgroup H // IsCompact (K : Set H)},
      ∃ L : {K : Subgroup H // IsCompact (K : Set H)},
        (⋃ K ∈ s, (K.1 : Set H)) ⊆ (L.1 : Set H)) →
    ∀ (E : Type uV) [AddCommGroup E] [Module ℂ E] (τ : Representation ℂ H E)
      (hτ : IsSmooth τ) (v : E),
      v ∈ relations τ ⊤ ↔
        ∃ (K : Subgroup H) (hK : IsCompact (K : Set H)),
          letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
          letI : MeasurableSpace K := borel K
          haveI : BorelSpace K := ⟨rfl⟩
          ∀ (μK : Measure K) [μK.IsHaarMeasure],
            (Hecke.fixedProjection μK (τ.comp K.subtype)
              (isSmooth_comp K.subtype continuous_subtype_val hτ) ⊤ isCompact_univ v : E) = 0

/-- Renard III.2.9, Corollary, first assertion: under the same hypothesis, for a
subrepresentation `E′` of a smooth representation `E`, `E′(H, τ′) = E(H, τ) ∩ E′`. -/
def CoinvariantSubrepresentationRelationsStatement : Prop :=
  ∀ (H : Type uH) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [TotallyDisconnectedSpace H],
    (⋃ K : {K : Subgroup H // IsCompact (K : Set H)}, (K.1 : Set H)) = Set.univ →
    (∀ s : Finset {K : Subgroup H // IsCompact (K : Set H)},
      ∃ L : {K : Subgroup H // IsCompact (K : Set H)},
        (⋃ K ∈ s, (K.1 : Set H)) ⊆ (L.1 : Set H)) →
    ∀ (E : Type uV) [AddCommGroup E] [Module ℂ E] (τ : Representation ℂ H E),
      IsSmooth τ →
      ∀ E' : Subrepresentation τ,
        (relations E'.toRepresentation ⊤).map E'.toSubmodule.subtype =
          relations τ ⊤ ⊓ E'.toSubmodule

end Langlands.Jacquet
