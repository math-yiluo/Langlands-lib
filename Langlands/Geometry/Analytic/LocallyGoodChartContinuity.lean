import Langlands.Geometry.Analytic.GoodChartContinuity
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.RefinementGluing

/-! # Continuity of analytic actions from local covers by good charts -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set Filter Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, v} (K := K)}
  {G : Type z} [Group G] [TopologicalSpace G]

/-- On a Hausdorff space, a chart covered by finitely many good charts is good.
The covering charts need not lie inside the given chart. -/
theorem IsGoodChart.of_cover [T2Space (localizedSpaceFunctor.obj X)]
    {σ : G →* Aut X} {W : (presentationOf X).presentation.atlas.Index}
    {s : Set (presentationOf X).presentation.atlas.Index} (hs : s.Finite)
    (hgood : ∀ c ∈ s, IsGoodChart σ c)
    (hcov : range ((presentationOf X).presentation.atlas.chart W) ⊆
      ⋃ c ∈ s, range ((presentationOf X).presentation.atlas.chart c)) :
    IsGoodChart σ W := by
  let S := presentationOf X
  have : T2Space S.presentation.space := ‹T2Space (localizedSpaceFunctor.obj X)›
  have hcomp : ∀ c, IsCompact (range (S.presentation.atlas.chart W) ∩
      range (S.presentation.atlas.chart c)) := fun c =>
    (isCompact_range (S.presentation.atlas.isEmbedding_chart W).continuous).inter_right
      (isCompact_range (S.presentation.atlas.isEmbedding_chart c).continuous).isClosed
  choose σc hσfin hσsub hσin hσcov using fun c : s =>
    S.presentation.atlas.isNet_chartFamily.exists_finite_cover_of_subset_inter
      (mem_range_self W) (mem_range_self c.val) (hcomp c.val) subset_rfl
  let t : Set S.presentation.atlas.Index :=
    ⋃ c : s, (fun k => range (S.presentation.atlas.chart k)) ⁻¹' σc c
  have : Finite s := hs.to_subtype
  have ht : t.Finite := Set.finite_iUnion fun c =>
    (hσfin c).preimage S.presentation.atlas.chartDomain_injective.injOn
  apply IsGoodChart.of_finite_cover ht
  · intro k hk
    obtain ⟨c, hkc⟩ := mem_iUnion.mp hk
    exact (hgood c c.property).of_subset ((hσin c _ hkc).trans inter_subset_right)
  · intro k hk
    obtain ⟨c, hkc⟩ := mem_iUnion.mp hk
    exact (hσin c _ hkc).trans inter_subset_left
  · rintro y hy
    obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.mp (hcov hy)
    obtain ⟨V, hV, hyV⟩ := hσcov ⟨c, hc⟩ ⟨hy, hyc⟩
    obtain ⟨k, rfl⟩ := hσsub ⟨c, hc⟩ hV
    exact mem_iUnion₂.mpr ⟨k, mem_iUnion.mpr ⟨⟨c, hc⟩, hV⟩, hyV⟩

/-- An action is locally good when every point has finitely many good charts
through it whose union is a neighbourhood of the point. -/
def IsLocallyGood (σ : G →* Aut X) : Prop :=
  ∀ y : (presentationOf X).presentation.space,
    (presentationOf X).IsLocallyChartCovered (IsGoodChart σ) Set.univ y

/-- Berkovich continuity from local covers by good charts: on a Hausdorff
analytic space, every locally good action is continuous. -/
theorem isContinuousAction_of_locallyGood [T2Space (localizedSpaceFunctor.obj X)]
    {σ : G →* Aut X} (h : IsLocallyGood σ) :
    IsContinuousAction σ := by
  intro τ
  let S := presentationOf X
  choose σy hσfin hσmem N hN hNcov using h
  have hWc : IsCompact (range (S.presentation.atlas.chart τ.domain)) :=
    isCompact_range (S.presentation.atlas.isEmbedding_chart τ.domain).continuous
  obtain ⟨t, -, ht⟩ := hWc.elim_nhds_subcover N (fun y _ => hN y)
  let s : Set S.presentation.atlas.Index := ⋃ y ∈ t, σy y
  have hs : s.Finite := t.finite_toSet.biUnion fun y _ => hσfin y
  have hW : IsGoodChart σ τ.domain := by
    apply IsGoodChart.of_cover hs
    · intro c hc
      obtain ⟨y, -, hcy⟩ := mem_iUnion₂.mp hc
      exact (hσmem y c hcy).2.2
    · intro z hz
      obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp (ht hz)
      obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp (hNcov y ⟨mem_univ z, hzy⟩)
      exact mem_iUnion₂.mpr ⟨c, mem_iUnion₂.mpr ⟨y, hy, hc⟩, hzc⟩
  filter_upwards [hW.1, hW.2 τ.function τ.bound τ.bound_pos] with g hg hb
  exact isNear_id_of_spectralBound_preservedChartPullback τ hg hb

end Langlands.Analytic.SaturatedAtlasPresentation
