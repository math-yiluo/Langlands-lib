import Langlands.Geometry.Analytic.InvariantAnalyticDomains
import Langlands.Geometry.Analytic.FibreProductOpenSubsystem
import Langlands.Geometry.Analytic.AtlasSubspaceRestriction
import Langlands.Geometry.Analytic.AtlasTopology.CompactSubcover

/-! # Open subspaces and finite local chart covers in saturated atlases -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open Set Topology Filter
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Refine one original chart through a point to an original chart contained
in an ambient open patch, retaining a relative neighborhood of the point. -/
theorem exists_subchart_nhdsWithin_open (ha : a.HasAllLocalDomains)
    {U : Set X} (hU : IsOpen U) (i : a.Index) {x : X}
    (hxi : x ∈ range (a.chart i)) (hxU : x ∈ U) :
    ∃ j : a.Index, range (a.chart j) ⊆ range (a.chart i) ∩ U ∧
      x ∈ range (a.chart j) ∧ range (a.chart j) ∈ 𝓝[range (a.chart i)] x := by
  obtain ⟨t, rfl⟩ := hxi
  obtain ⟨j, hji, hjN, hjU⟩ := a.exists_subchart_neighborhood ha i t
    (a.chart i ⁻¹' U) ((hU.preimage (a.isEmbedding_chart i).continuous).mem_nhds hxU)
  have hN : range (a.chart j) ∈ 𝓝[range (a.chart i)] (a.chart i t) := by
    rw [← (a.isEmbedding_chart i).map_nhds_eq]
    exact hjN
  refine ⟨j, ?_, (show t ∈ a.chart i ⁻¹' range (a.chart j) from
    mem_of_mem_nhds hjN), hN⟩
  intro y hy
  refine ⟨hji hy, ?_⟩
  obtain ⟨s, rfl⟩ := hji hy
  exact hjU hy

/-- A compact subset of an open part of a two-chart intersection has a
finite cover by original charts contained in both charts and the open part. -/
theorem exists_finite_charts_cover_inter_open (ha : a.HasAllLocalDomains)
    {U T : Set X} (hU : IsOpen U) (hT : IsCompact T)
    (i j : a.Index) (hTsub : T ⊆ (range (a.chart i) ∩ range (a.chart j)) ∩ U) :
    ∃ S : Set a.Index, S.Finite ∧
      (∀ k ∈ S, range (a.chart k) ⊆ (range (a.chart i) ∩ range (a.chart j)) ∩ U) ∧
      T ⊆ ⋃ k ∈ S, range (a.chart k) := by
  have hnet := a.isNet_chartFamily
  have hdom := hnet.isQuasinet_restrictedFamily_inter
    (hnet.2 _ ⟨i, rfl⟩ _ ⟨j, rfl⟩) (ha.isOriginalChartDomain_of_isOpen hU)
  obtain ⟨σ, hσ, hσa, hσsub, hcov⟩ :=
    AtlasTopology.exists_finite_cover_of_restrictedFamily hdom hT hTsub
  refine ⟨{k | range (a.chart k) ∈ σ},
    hσ.preimage a.chartDomain_injective.injOn, fun k hk => hσsub _ hk, ?_⟩
  intro x hx
  obtain ⟨W, hWσ, hxW⟩ := hcov hx
  obtain ⟨k, rfl⟩ := hσa hWσ
  exact mem_biUnion hWσ hxW

/-- Two original charts contained in a Hausdorff subspace have compact
intersection in the ambient space, even when the ambient space is not Hausdorff. -/
theorem isCompact_inter_of_subset_t2Space {U : Set X} [T2Space U]
    (i j : a.Index) (hiU : range (a.chart i) ⊆ U) (hjU : range (a.chart j) ⊆ U) :
    IsCompact (range (a.chart i) ∩ range (a.chart j)) := by
  have hci : IsCompact (Subtype.val ⁻¹' range (a.chart i) : Set U) :=
    IsInducing.subtypeVal.isCompact_preimage'
      (isCompact_range (a.isEmbedding_chart i).continuous)
      (by simpa only [Subtype.range_coe] using hiU)
  have hcj : IsCompact (Subtype.val ⁻¹' range (a.chart j) : Set U) :=
    IsInducing.subtypeVal.isCompact_preimage'
      (isCompact_range (a.isEmbedding_chart j).continuous)
      (by simpa only [Subtype.range_coe] using hjU)
  have hc := (hci.inter hcj).image continuous_subtype_val
  have heq : Subtype.val ''
      ((Subtype.val ⁻¹' range (a.chart i) : Set U) ∩
        Subtype.val ⁻¹' range (a.chart j)) =
      range (a.chart i) ∩ range (a.chart j) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hiU hx.1⟩, hx, rfl⟩
  rwa [heq] at hc

/-- Finite intersection covers only require a Hausdorff subspace containing
the two charts, rather than a globally Hausdorff ambient atlas. -/
theorem exists_finite_charts_inter_of_subset_t2Space {U : Set X} [T2Space U]
    (i j : a.Index) (hiU : range (a.chart i) ⊆ U) (hjU : range (a.chart j) ⊆ U) :
    ∃ S : Set a.Index, S.Finite ∧
      (∀ k ∈ S, range (a.chart k) ⊆ range (a.chart i) ∩ range (a.chart j)) ∧
      range (a.chart i) ∩ range (a.chart j) ⊆ ⋃ k ∈ S, range (a.chart k) := by
  obtain ⟨σ, hσ, hσa, hσsub, hcov⟩ :=
    a.isNet_chartFamily.exists_finite_cover_of_subset_inter ⟨i, rfl⟩ ⟨j, rfl⟩
      (a.isCompact_inter_of_subset_t2Space i j hiU hjU) subset_rfl
  refine ⟨{k | range (a.chart k) ∈ σ},
    hσ.preimage a.chartDomain_injective.injOn, fun k hk => hσsub _ hk, ?_⟩
  intro x hx
  obtain ⟨W, hWσ, hxW⟩ := hcov hx
  obtain ⟨k, rfl⟩ := hσa hWσ
  exact mem_biUnion hWσ hxW

/-- The actual original-chart atlas on an open subspace of a
domain-saturated atlas, with its finite-neighborhood condition proved above. -/
def openSubspaceAtlas (ha : a.HasAllLocalDomains) {U : Set X} (hU : IsOpen U) :
    IndexedAffinoidAtlas.{u, v, w} K U :=
  a.subspaceAtlas U (ha.isOriginalChartDomain_of_isOpen hU)

end Langlands.Analytic.IndexedAffinoidAtlas
