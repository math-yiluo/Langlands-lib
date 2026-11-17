import Langlands.Geometry.Analytic.RecognizedOpenImageCover
import Langlands.Geometry.Analytic.RecognizedDomainMapCompatibility

/-! # Pointed recognized neighborhoods with controlled target images -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

/-- A compact subset of an open Hausdorff patch can be avoided near a
point of that patch which it does not contain, without ambient separation. -/
theorem compact_compl_mem_nhds_in_open_patch
    {X : Type v} [TopologicalSpace X] {O T : Set X} (hO : IsOpen O)
    [T2Space O] (hT : IsCompact T) (hTO : T ⊆ O) {x : X}
    (hxO : x ∈ O) (hxT : x ∉ T) : Tᶜ ∈ 𝓝 x := by
  let j : O → X := Subtype.val
  have hclosed : IsClosed (j ⁻¹' T) :=
    (IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hT
      (fun y hy => ⟨⟨y, hTO hy⟩, rfl⟩)).isClosed
  have hopen : IsOpen (j '' (j ⁻¹' T)ᶜ) :=
    hO.isOpenEmbedding_subtypeVal.isOpenMap _ hclosed.isOpen_compl
  apply Filter.mem_of_superset (hopen.mem_nhds ⟨⟨x, hxO⟩, hxT, rfl⟩)
  rintro y ⟨z, hz, rfl⟩
  exact hz

/-- Retaining the members through the point of a finite compact family
still covers a neighborhood, if the original union does. Separation is
needed only on a given open containing patch. -/
theorem finite_compact_pointed_union_mem_nhds
    {X : Type v} [TopologicalSpace X] {O : Set X} (hO : IsOpen O) [T2Space O]
    {ι : Type w} [Finite ι] (T : ι → Set X) (hc : ∀ i, IsCompact (T i))
    (hTO : ∀ i, T i ⊆ O) {x : X} (hxO : x ∈ O)
    (hN : (⋃ i, T i) ∈ 𝓝 x) : (⋃ i, ⋃ (_ : x ∈ T i), T i) ∈ 𝓝 x := by
  classical
  have havoid : ∀ i, (if x ∈ T i then univ else (T i)ᶜ) ∈ 𝓝 x := by
    intro i
    split_ifs with hi
    · exact Filter.univ_mem
    · exact compact_compl_mem_nhds_in_open_patch hO (hc i) (hTO i) hxO hi
  have hall : (⋂ i, if x ∈ T i then univ else (T i)ᶜ) ∈ 𝓝 x :=
    Filter.iInter_mem.mpr havoid
  apply Filter.mem_of_superset (Filter.inter_mem hN hall)
  rintro y ⟨hy, hya⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  have hxi : x ∈ T i := by
    by_contra hxi
    have hai := mem_iInter.mp hya i
    simp only [hxi, ↓reduceIte] at hai
    exact hai hi
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hxi, hi⟩⟩

namespace AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  (g : StrongHom A.saturatedPresentation B.saturatedPresentation)

/-- Every point mapping into an open base set admits a finite pointed
recognized neighborhood family inside a prescribed open Hausdorff source
patch; each entire image lies in one recognized base piece inside that set. -/
theorem exists_finite_recognized_image_neighborhoods
    {x : A.space} (O : Set A.space) (hO : IsOpen O) [T2Space O] (hxO : x ∈ O)
    (U : Set B.space) (hU : IsOpen U) (hxU : g.baseMap x ∈ U) :
    ∃ I : Set A.atlas.saturatedAtlas.RecognizedSubset, I.Finite ∧
      (∀ R ∈ I, x ∈ R.locus ∧ R.locus ⊆ O ∧
        ∃ W : B.atlas.saturatedAtlas.RecognizedSubset,
          W.locus ⊆ U ∧ g.baseMap '' R.locus ⊆ W.locus) ∧
      (⋃ R ∈ I, R.locus) ∈ 𝓝 x := by
  classical
  let E := O ∩ g.baseMap ⁻¹' U
  have hE : E ∈ 𝓝 x :=
    (hO.inter (hU.preimage g.baseMap.continuous)).mem_nhds ⟨hxO, hxU⟩
  obtain ⟨J, hJ, hJE, hJN⟩ := A.atlas.exists_finite_recognized_nhds_subset x E hE
  let _ := hJ.fintype
  let C (R : J) := g.recognizedOpenImageCover R.val U hU (by
    rintro b ⟨a, ha, hb⟩
    exact hb ▸ ((hJE R.val R.property).2 ha).2)
  let Z := Σ R : J, Fin (C R).cover.size
  let F (z : Z) := g.domainRecognition z.1.val ((C z.1).cover.obj z.2)
  have hFlocus (z : Z) : (F z).locus =
      z.1.val.chart '' ((C z.1).cover.obj z.2).locus := rfl
  have hFO (z : Z) : (F z).locus ⊆ O := by
    rw [hFlocus]
    rintro y ⟨t, -, rfl⟩
    exact ((hJE z.1.val z.1.property).2 (z.1.val.range_chart.subset ⟨t, rfl⟩)).1
  have hFU (z : Z) : g.baseMap '' (F z).locus ⊆ ((C z.1).target z.2).locus := by
    rw [hFlocus]
    rintro _ ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    obtain ⟨s, hs⟩ := ((C z.1).cover.obj z.2).represents.2.1.symm ▸ ht
    exact ((C z.1).target z.2).range_chart.subset
      ⟨_, ((C z.1).chart_comm z.2 s).trans
        (congrArg (fun q => g.baseMap (z.1.val.chart q)) hs)⟩
  have hFN : (⋃ z, (F z).locus) ∈ 𝓝 x := by
    apply Filter.mem_of_superset hJN
    rintro y hy
    obtain ⟨R, hR, hyR⟩ := mem_iUnion₂.mp hy
    obtain ⟨t, ht⟩ := R.range_chart.symm ▸ hyR
    obtain ⟨i, hi⟩ := (C ⟨R, hR⟩).cover.covers t (mem_univ t)
    refine mem_iUnion.mpr ⟨⟨⟨R, hR⟩, i⟩, ?_⟩
    rw [hFlocus]
    exact ⟨t, hi, ht⟩
  have hpoint : (⋃ z, ⋃ (_ : x ∈ (F z).locus), (F z).locus) ∈ 𝓝 x :=
    finite_compact_pointed_union_mem_nhds hO (fun z => (F z).locus)
      (fun z => (F z).range_chart ▸ isCompact_range (F z).chart.continuous) hFO hxO hFN
  let I := {R : A.atlas.saturatedAtlas.RecognizedSubset | ∃ z : Z, F z = R ∧ x ∈ R.locus}
  refine ⟨I, (Set.finite_range F).subset (fun _ ⟨z, hz, _⟩ => ⟨z, hz⟩), ?_, ?_⟩
  · rintro R ⟨z, rfl, hx⟩
    exact ⟨hx, hFO z, (C z.1).target z.2, (C z.1).target_subset z.2, hFU z⟩
  · apply Filter.mem_of_superset hpoint
    rintro y hy
    obtain ⟨z, hx, hy⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨F z, ⟨z, rfl, hx⟩, hy⟩

/-- A finite pointed recognized neighborhood family with a chosen actual
recognized target for every entire image. -/
structure RecognizedImageNeighborhoods
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (x : A.space) (O : Set A.space) (U : Set B.space) where
  family : Set A.atlas.saturatedAtlas.RecognizedSubset
  finite : family.Finite
  source : ∀ R ∈ family, x ∈ R.locus ∧ R.locus ⊆ O
  target : ∀ R ∈ family, B.atlas.saturatedAtlas.RecognizedSubset
  target_subset : ∀ R hR, (target R hR).locus ⊆ U
  image : ∀ R hR, g.baseMap '' R.locus ⊆ (target R hR).locus
  neighborhood : (⋃ R ∈ family, R.locus) ∈ 𝓝 x

/-- The family and chosen targets are constructed from rational target
pullbacks and the finite compact refinement, including boundary points. -/
def recognizedImageNeighborhoods
    {x : A.space} (O : Set A.space) (hO : IsOpen O) [T2Space O] (hxO : x ∈ O)
    (U : Set B.space) (hU : IsOpen U) (hxU : g.baseMap x ∈ U) :
    RecognizedImageNeighborhoods g x O U :=
  let h := g.exists_finite_recognized_image_neighborhoods O hO hxO U hU hxU
  { family := h.choose
    finite := h.choose_spec.1
    source R hR := ⟨(h.choose_spec.2.1 R hR).1, (h.choose_spec.2.1 R hR).2.1⟩
    target R hR := (h.choose_spec.2.1 R hR).2.2.choose
    target_subset R hR := (h.choose_spec.2.1 R hR).2.2.choose_spec.1
    image R hR := (h.choose_spec.2.1 R hR).2.2.choose_spec.2
    neighborhood := h.choose_spec.2.2 }

end AffinoidAtlasPresentation.StrongHom
end Langlands.Analytic
