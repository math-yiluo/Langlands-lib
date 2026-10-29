import Langlands.Topology.GroupAction.InducedCharts
import Langlands.Geometry.Analytic.AtlasTopology.QuasinetProperties

/-! # Compact coset charts of an induced space -/

noncomputable section

universe u v

namespace Langlands.TopologicalInduction

open Set Topology
open scoped Topology

variable {G : Type u} [Group G] (H : Subgroup G)
  {X : Type v} [MulAction H X]

/-- The actual family of fibers of the induced space's left-coset map. -/
def cosetChartFamily : Set (Set (Space H X)) :=
  Set.range (fun c : G ⧸ H => (component H : Space H X → G ⧸ H) ⁻¹' {c})

theorem fiber_mem_cosetChartFamily (c : G ⧸ H) :
    (component H : Space H X → G ⧸ H) ⁻¹' {c} ∈ cosetChartFamily H :=
  ⟨c, rfl⟩

theorem range_chart_mem_cosetChartFamily (g : G) :
    Set.range (chart H g : X → Space H X) ∈ cosetChartFamily H := by
  rw [range_chart_eq_fiber]
  exact fiber_mem_cosetChartFamily H _

section Topology

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]

theorem isClopen_component_fiber (hH : IsOpen (H : Set G)) (c : G ⧸ H) :
    IsClopen ((component H : Space H X → G ⧸ H) ⁻¹' {c}) := by
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  exact (isClopen_discrete {c}).preimage (continuous_component H)

/-- Each point's own open coset fiber supplies a singleton quasinet witness. -/
theorem isQuasinet_cosetChartFamily (hH : IsOpen (H : Set G)) :
    Analytic.AtlasTopology.IsQuasinet (cosetChartFamily H (X := X)) := by
  intro z
  let U : Set (Space H X) := component H ⁻¹' {component H z}
  refine ⟨{U}, Set.finite_singleton _, ?_, ?_, ?_⟩
  · simpa only [Set.singleton_subset_iff] using
      fiber_mem_cosetChartFamily H (component H z)
  · intro V hV
    have he : V = U := Set.mem_singleton_iff.mp hV
    subst V
    rfl
  · rw [Set.sUnion_singleton]
    exact (isClopen_component_fiber H hH _).isOpen.mem_nhds rfl

/-- At a point of an intersection, both coset labels coincide; the restricted
family then contains the whole intersection. -/
theorem isNet_cosetChartFamily (hH : IsOpen (H : Set G)) :
    Analytic.AtlasTopology.IsNet (cosetChartFamily H (X := X)) := by
  refine ⟨isQuasinet_cosetChartFamily H hH, ?_⟩
  rintro U ⟨c, rfl⟩ V ⟨d, rfl⟩ z
  have hcd : c = d := z.property.1.symm.trans z.property.2
  subst d
  apply Analytic.AtlasTopology.isQuasinet_of_univ_mem (τ :=
    Analytic.AtlasTopology.restrictedFamily (cosetChartFamily H)
      ((component H ⁻¹' {c}) ∩ (component H ⁻¹' {c}))) ?_ z
  refine ⟨component H ⁻¹' {c}, fiber_mem_cosetChartFamily H c, ?_, ?_⟩
  · exact fun y hy => ⟨hy, hy⟩
  · ext y
    exact ⟨fun _ => y.property.1, fun _ => Set.mem_univ _⟩

/-- Compact subsets of the induced space have only finitely many coset labels.
No compactness or separation hypothesis on the original space is needed. -/
theorem finite_component_image_of_isCompact (hH : IsOpen (H : Set G))
    {s : Set (Space H X)} (hs : IsCompact s) : (component H '' s).Finite := by
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  exact (hs.image (continuous_component H)).finite_of_discrete

theorem exists_finite_chart_cover_of_isCompact (hH : IsOpen (H : Set G))
    {s : Set (Space H X)} (hs : IsCompact s) :
    ∃ C : Finset (G ⧸ H), s ⊆ ⋃ c ∈ C, Set.range (chart H c.out : X → Space H X) := by
  classical
  have hc := finite_component_image_of_isCompact H hH hs
  refine ⟨hc.toFinset, ?_⟩
  intro z hz
  have hm : component H z ∈ hc.toFinset := hc.mem_toFinset.mpr ⟨z, hz, rfl⟩
  refine Set.mem_iUnion.mpr ⟨component H z, Set.mem_iUnion.mpr ⟨hm, ?_⟩⟩
  rw [range_chart_eq_fiber, QuotientGroup.out_eq']
  rfl

section ContinuousAction

variable [ContinuousSMul H X]

/-- Every fiber is the continuous image of the original compact space. -/
theorem isCompact_of_mem_cosetChartFamily [CompactSpace X] {U : Set (Space H X)}
    (hU : U ∈ cosetChartFamily H) : IsCompact U := by
  rcases hU with ⟨c, rfl⟩
  simpa only [range_chart_eq_fiber, QuotientGroup.out_eq'] using
    isCompact_range (continuous_chart H (X := X) c.out)

/-- Transfer Hausdorffness from the actual coproduct of coset copies. -/
theorem t2Space_induced [T2Space X] (hH : IsOpen (H : Set G)) :
    T2Space (Space H X) :=
  (cosetCopiesHomeomorph H (X := X) hH).t2Space

theorem isCompactFamily_cosetChartFamily [CompactSpace X] [T2Space X]
    (hH : IsOpen (H : Set G)) :
    Analytic.AtlasTopology.IsCompactFamily (cosetChartFamily H (X := X)) := by
  let := t2Space_induced H (X := X) hH
  intro U hU
  exact ⟨isCompact_of_mem_cosetChartFamily H hU, inferInstance⟩

/-- The compact coset quasinet gives compact neighborhoods. -/
theorem locallyCompactSpace_induced [CompactSpace X] [T2Space X]
    (hH : IsOpen (H : Set G)) : LocallyCompactSpace (Space H X) := by
  let := t2Space_induced H (X := X) hH
  exact (isQuasinet_cosetChartFamily H (X := X) hH).locallyCompactSpace
    fun U hU => isCompact_of_mem_cosetChartFamily H hU

end ContinuousAction

end Topology

end Langlands.TopologicalInduction
