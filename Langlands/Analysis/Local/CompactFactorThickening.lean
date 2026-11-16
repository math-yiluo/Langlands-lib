import Langlands.Analysis.Local.RightInvariantFactorizationIntegral
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Compact neighborhoods invariant under a compact right factor -/

noncomputable section

namespace Langlands.CompactFactorization

open MeasureTheory Set Topology
open scoped Pointwise ENNReal

variable {G : Type*} [Group G]

/-- Thicken a set by a subgroup on the right. -/
def rightFactorThickening (K : Subgroup G) (U : Set G) : Set G :=
  U * (K : Set G)

theorem subset_rightFactorThickening (K : Subgroup G) (U : Set G) :
    U ⊆ rightFactorThickening K U := by
  intro u hu
  exact ⟨u, hu, 1, K.one_mem, mul_one u⟩

theorem rightSubgroupInvariant_rightFactorThickening
    (K : Subgroup G) (U : Set G) :
    RightSubgroupInvariant K (rightFactorThickening K U) := by
  intro g k hk
  constructor
  · rintro ⟨u, hu, l, hl, heq⟩
    change u * l = g * k at heq
    refine ⟨u, hu, l * k⁻¹, K.mul_mem hl (K.inv_mem hk), ?_⟩
    calc
      u * (l * k⁻¹) = (u * l) * k⁻¹ := (mul_assoc _ _ _).symm
      _ = g := by rw [heq]; simp
  · rintro ⟨u, hu, l, hl, rfl⟩
    exact ⟨u, hu, l * k, K.mul_mem hl hk, (mul_assoc _ _ _).symm⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isCompact_rightFactorThickening (K : Subgroup G) (U : Set G)
    (hK : IsCompact (K : Set G)) (hU : IsCompact U) :
    IsCompact (rightFactorThickening K U) :=
  hU.mul hK

omit [IsTopologicalGroup G] in
theorem rightFactorThickening_mem_nhds (K : Subgroup G) (U : Set G)
    (hU : U ∈ 𝓝 (1 : G)) :
    rightFactorThickening K U ∈ 𝓝 (1 : G) :=
  Filter.mem_of_superset hU (subset_rightFactorThickening K U)

/-- A compact subgroup has a compact neighborhood of one invariant under
right multiplication by that subgroup. -/
theorem exists_compact_rightSubgroupInvariant_neighborhood
    [LocallyCompactSpace G]
    (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    ∃ C : Set G, IsCompact C ∧ C ∈ 𝓝 (1 : G) ∧ RightSubgroupInvariant K C := by
  obtain ⟨U, hUc, hUn⟩ := exists_compact_mem_nhds (1 : G)
  exact ⟨rightFactorThickening K U, hUc.mul hK,
    rightFactorThickening_mem_nhds K U hUn,
    rightSubgroupInvariant_rightFactorThickening K U⟩

/-- The inverse-coordinate mass of a compact neighborhood in a closed subgroup
is positive and finite for every measure positive on open sets and finite on
compact sets. In particular this applies to every Haar normalization. -/
theorem subgroup_inverse_neighborhood_mass_pos_lt_top
    [T2Space G] (P : Subgroup G) (hP : IsClosed (P : Set G))
    [MeasurableSpace P] [BorelSpace P]
    (ρ : Measure P) [Measure.IsOpenPosMeasure ρ] [IsFiniteMeasureOnCompacts ρ]
    (C : Set G) (hC : IsCompact C) (hCn : C ∈ 𝓝 (1 : G)) :
    0 < ρ {p : P | (p : G)⁻¹ ∈ C} ∧ ρ {p : P | (p : G)⁻¹ ∈ C} < ⊤ := by
  have hn : {p : P | (p : G)⁻¹ ∈ C} ∈ 𝓝 (1 : P) := by
    have hc : Continuous (fun p : P => (p : G)⁻¹) := continuous_subtype_val.inv
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hCn)
  have hc : IsCompact {p : P | (p : G)⁻¹ ∈ C} :=
    ((Homeomorph.inv G).isClosedEmbedding.comp
      hP.isClosedEmbedding_subtypeVal).isCompact_preimage hC
  exact ⟨Measure.measure_pos_of_mem_nhds ρ hn, hc.measure_lt_top⟩

end Langlands.CompactFactorization
