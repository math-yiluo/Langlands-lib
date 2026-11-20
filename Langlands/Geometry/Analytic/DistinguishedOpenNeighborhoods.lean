import Langlands.Geometry.Analytic.AtlasTopology.CompactSubcover
import Langlands.Geometry.Analytic.DistinguishedOpenRestriction
import Langlands.Geometry.Analytic.LocalizedCompactNeighborhoods
import Langlands.Geometry.Analytic.RecognizedDomainSaturationSite

/-! # Stable distinguished open neighborhoods -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

open CategoryTheory Filter Set Topology
open scoped Topology Pointwise

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {Y : Type v} [TopologicalSpace Y] (a : IndexedAffinoidAtlas.{u, v, w} K Y)

private theorem isOriginalChartDomain_of_openLocal {S : Set Y}
    (h : ∀ y ∈ S, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ a.IsOriginalChartDomain (S ∩ V)) :
    a.IsOriginalChartDomain S := by
  apply (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mpr
  rintro _ ⟨rfl⟩ y hy
  obtain ⟨V, hV, hyV, hD⟩ := h y hy
  obtain ⟨σ, hf, hs, hm, hn⟩ :=
    (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp hD _ (mem_singleton _) y ⟨hy, hyV⟩
  refine ⟨σ, hf, hs, fun W hW => ⟨(hm W hW).1.trans inter_subset_left, (hm W hW).2⟩, ?_⟩
  rwa [nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hyV))] at hn

private theorem isCompact_chartUnion {I : Set a.Index} (hI : I.Finite) :
    IsCompact (⋃ i ∈ I, range (a.chart i)) :=
  hI.isCompact_biUnion fun i _ => isCompact_range (a.isEmbedding_chart i).continuous

private theorem isOriginalChartDomain_chartUnion [T2Space Y] {I : Set a.Index} (hI : I.Finite) :
    a.IsOriginalChartDomain (⋃ i ∈ I, range (a.chart i)) := by
  let := hI.fintype
  apply a.isOriginalChartDomain_of_finite_chart_cover _ (fun i : I => i.val)
  exact iUnion_subtype _ _

private theorem exists_distinguished_chart_difference [T2Space Y] (ha : a.HasAllLocalDomains)
    {x : Y} {V : Set Y} (hV : IsOpen V) (hx : x ∈ V) :
    ∃ I J : Set a.Index, I.Finite ∧ J.Finite ∧
      let U := (⋃ i ∈ I, range (a.chart i)) \ (⋃ j ∈ J, range (a.chart j))
      IsOpen U ∧ a.IsOriginalChartDomain Uᶜ ∧ x ∈ U ∧
        closure U ⊆ V ∧ IsCompact (closure U) := by
  let := a.locallyCompactSpace
  obtain ⟨I, hI, hIV, hCn⟩ := ha.exists_finite_chart_nhds_subset a x V (hV.mem_nhds hx)
  let C := ⋃ i ∈ I, range (a.chart i)
  have hCV : C ⊆ V := iUnion₂_subset fun i hi => (hIV i hi).2
  have hxC : x ∈ interior C := mem_interior_iff_mem_nhds.mpr hCn
  obtain ⟨W, hWo, hxW, hWc, hWcomp⟩ := exists_open_between_and_isCompact_closure
    (K := {x}) isCompact_singleton isOpen_interior (singleton_subset_iff.mpr hxC)
  have hcut : a.IsOriginalChartDomain (C ∩ {x}ᶜ) :=
    (a.isOriginalChartDomain_chartUnion hI).inter a
      (ha.isOriginalChartDomain_of_isOpen isClosed_singleton.isOpen_compl)
  have hCW : C \ W ⊆ C ∩ {x}ᶜ := by
    rintro y ⟨hyC, hyW⟩
    exact ⟨hyC, fun hy => hyW (hxW hy)⟩
  obtain ⟨σ, hσ, hchart, hsub, hcover⟩ := AtlasTopology.exists_finite_cover_of_restrictedFamily
    hcut ((a.isCompact_chartUnion hI).diff hWo) hCW
  let J : Set a.Index := {j | range (a.chart j) ∈ σ}
  have hJ : J.Finite := hσ.preimage a.chartDomain_injective.injOn
  let B := ⋃ j ∈ J, range (a.chart j)
  have hB : B = ⋃₀ σ := by
    ext y
    constructor
    · intro hy
      obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hy
      exact ⟨_, hj, hyj⟩
    · rintro ⟨T, hT, hy⟩
      obtain ⟨j, rfl⟩ := hchart hT
      exact mem_iUnion₂.mpr ⟨j, hT, hy⟩
  have hBsub : B ⊆ C ∩ {x}ᶜ := iUnion₂_subset fun j hj => hsub _ hj
  have hUB : C \ B ⊆ W := by
    intro y hy
    by_contra hyW
    exact hy.2 (hB.symm ▸ hcover ⟨hy.1, hyW⟩)
  have hUeq : C \ B = W \ B :=
    Subset.antisymm (fun _ hy => ⟨hUB hy, hy.2⟩)
      (fun _ hy => ⟨interior_subset (hWc (subset_closure hy.1)), hy.2⟩)
  refine ⟨I, J, hI, hJ, ?_⟩
  change IsOpen (C \ B) ∧ a.IsOriginalChartDomain (C \ B)ᶜ ∧
    x ∈ C \ B ∧ closure (C \ B) ⊆ V ∧ IsCompact (closure (C \ B))
  refine ⟨hUeq.symm ▸ hWo.sdiff (a.isCompact_chartUnion hJ).isClosed, ?_,
    ⟨interior_subset hxC, fun h => (hBsub h).2 (mem_singleton x)⟩,
    (closure_mono hUB).trans (hWc.trans (interior_subset.trans hCV)),
    hWcomp.of_isClosed_subset isClosed_closure (closure_mono hUB)⟩
  apply a.isOriginalChartDomain_of_openLocal
  intro y hy
  by_cases hyC : y ∈ interior C
  · refine ⟨interior C, isOpen_interior, hyC, ?_⟩
    have h : (C \ B)ᶜ ∩ interior C = B ∩ interior C := by
      ext t
      by_cases ht : t ∈ interior C
      · simp [ht, interior_subset ht, Set.mem_sdiff]
      · simp [ht]
    rw [h]
    exact (a.isOriginalChartDomain_chartUnion hJ).inter a
      (ha.isOriginalChartDomain_of_isOpen isOpen_interior)
  · refine ⟨(closure W)ᶜ, isClosed_closure.isOpen_compl, fun hyW => hyC (hWc hyW), ?_⟩
    rw [inter_eq_right.mpr (compl_subset_compl.mpr (hUB.trans subset_closure))]
    exact ha.isOriginalChartDomain_of_isOpen isClosed_closure.isOpen_compl

end IndexedAffinoidAtlas

namespace SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, w} (K := K)}
  {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Each open neighborhood contains a distinguished open neighborhood with compact
closure inside it, preserved by an open subgroup of the analytic action. -/
def HasStableDistinguishedOpenNeighborhoods (ρ : G →* Aut X) : Prop :=
  let := localizedSpaceAction ρ
  ∀ (x : localizedSpaceFunctor.obj X) (V : Set (localizedSpaceFunctor.obj X)),
    IsOpen V → x ∈ V →
      ∃ (U : Set (localizedSpaceFunctor.obj X)) (H : OpenSubgroup G),
        IsDistinguishedOpen X U ∧ x ∈ U ∧ closure U ⊆ V ∧ IsCompact (closure U) ∧
          ∀ g ∈ H, g • U = U

/-- Berkovich continuity on a Hausdorff analytic space gives stable distinguished neighborhoods. -/
theorem hasStableDistinguishedOpenNeighborhoods [T2Space (localizedSpaceFunctor.obj X)]
    {ρ : G →* Aut X} (hρ : IsContinuousAction ρ) :
    HasStableDistinguishedOpenNeighborhoods ρ := by
  let := localizedSpaceAction ρ
  intro x V hV hx
  let _ : T2Space (presentationOf X).presentation.space :=
    inferInstanceAs (T2Space (localizedSpaceFunctor.obj X))
  let a := (presentationOf X).presentation.atlas
  obtain ⟨I, J, hI, hJ, hUo, hUd, hxU, hUV, hUc⟩ :=
    a.exists_distinguished_chart_difference (presentationOf X).hasAllLocalDomains hV hx
  let U : Set (localizedSpaceFunctor.obj X) :=
    (⋃ i ∈ I, range (a.chart i)) \ (⋃ j ∈ J, range (a.chart j))
  let := (hI.union hJ).fintype
  let H := OpenSubgroup.iInfOfFinite (fun i : ↥(I ∪ J) => chartOpenStabilizer ρ hρ i.val)
  refine ⟨U, H, ⟨hUo, hUd⟩, hxU, hUV, hUc, ?_⟩
  intro g hg
  have hInv (M : Set a.Index) (hM : M ⊆ I ∪ J) :
      g • (⋃ i ∈ M, range (a.chart i) : Set (localizedSpaceFunctor.obj X)) =
        ⋃ i ∈ M, range (a.chart i) := by
    rw [smul_set_iUnion₂]
    exact iUnion₂_congr fun i hi => OpenSubgroup.iInfOfFinite_le
      (fun j : ↥(I ∪ J) => chartOpenStabilizer ρ hρ j.val) ⟨i, hM hi⟩ hg
  exact (smul_set_sdiff (a := g)).trans (congrArg₂ (· \ ·)
    (hInv I subset_union_left) (hInv J subset_union_right))

end SaturatedAtlasPresentation
end Langlands.Analytic
