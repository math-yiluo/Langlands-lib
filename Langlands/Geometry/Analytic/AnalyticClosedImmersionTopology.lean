import Langlands.Geometry.Analytic.AnalyticClosedImmersionMonomorphism
import Mathlib.Topology.Maps.Proper.Basic

/-! # The underlying topology of analytic closed immersions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open Set Topology IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

private theorem exists_preimage_of_isFinite (hg : g.IsFinite)
    (i : B.atlas.saturatedAtlas.Index) :
    ∃ V : A.atlas.saturatedAtlas.RecognizedSubset,
      Set.range V.chart = g.baseMap ⁻¹' Set.range (B.atlas.saturatedAtlas.chart i) := by
  let W := B.atlas.saturatedAtlas.originalRecognitionIndex i
  obtain ⟨V, _, hV, _⟩ := hg.2 W (Set.subset_univ _)
  have hW : W.locus = Set.range (B.atlas.saturatedAtlas.chart i) :=
    W.range_chart.symm.trans (B.atlas.saturatedAtlas.recognitionAtlas_original_range i)
  refine ⟨V, ?_⟩
  rw [V.range_chart, hV, hW, Set.univ_inter]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A finite strong morphism is proper on underlying topological spaces.
This follows from the recognized affinoid preimages of the target charts. -/
theorem IsFinite.isProperMap (hg : g.IsFinite) : IsProperMap g.baseMap := by
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨g.baseMap.continuous, ?_, ?_⟩
  · intro S hS
    apply (B.atlas.saturatedAtlas.isNet_chartFamily.1.isClosed_iff _).mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨V, hV⟩ := exists_preimage_of_isFinite hg i
    let m : BanachSpectrum V.algebra → Set.range (B.atlas.saturatedAtlas.chart i) :=
      fun x => ⟨g.baseMap (V.chart x), hV.subset (mem_range_self x)⟩
    have hcont := (A.fullRecognitionPresentation.atlas.isEmbedding_chart V).continuous
    have hm : Continuous m := (g.baseMap.continuous.comp hcont).subtype_mk _
    let : T2Space (Set.range (B.atlas.saturatedAtlas.chart i)) :=
      (B.atlas.saturatedAtlas.isEmbedding_chart i).toHomeomorph.t2Space
    have heq : Subtype.val ⁻¹' (g.baseMap '' S) = m '' (V.chart ⁻¹' S) := by
      ext y
      constructor
      · rintro ⟨x, hx, hxy⟩
        have hx' : x ∈ Set.range V.chart := hV.superset (show g.baseMap x ∈ _ from hxy ▸ y.property)
        obtain ⟨z, rfl⟩ := hx'
        exact ⟨z, hx, Subtype.ext hxy⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨V.chart x, hx, rfl⟩
    rw [heq]
    exact ((hS.preimage hcont).isCompact.image hm).isClosed
  · intro y
    obtain ⟨i, hi⟩ := B.atlas.saturatedAtlas.exists_chart_at y
    obtain ⟨V, hV⟩ := exists_preimage_of_isFinite hg i
    let m : BanachSpectrum V.algebra → Set.range (B.atlas.saturatedAtlas.chart i) :=
      fun x => ⟨g.baseMap (V.chart x), hV.subset (mem_range_self x)⟩
    have hcont := (A.fullRecognitionPresentation.atlas.isEmbedding_chart V).continuous
    have hm : Continuous m := (g.baseMap.continuous.comp hcont).subtype_mk _
    let : T2Space (Set.range (B.atlas.saturatedAtlas.chart i)) :=
      (B.atlas.saturatedAtlas.isEmbedding_chart i).toHomeomorph.t2Space
    have heq : g.baseMap ⁻¹' {y} = V.chart '' (m ⁻¹' {⟨y, hi⟩}) := by
      ext x
      constructor
      · intro hx
        have hxy : g.baseMap x = y := Set.mem_singleton_iff.mp hx
        have hx' : x ∈ Set.range V.chart := hV.superset (show g.baseMap x ∈ _ from hxy ▸ hi)
        obtain ⟨z, rfl⟩ := hx'
        exact ⟨z, Set.mem_singleton_iff.mpr (Subtype.ext hxy), rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact Set.mem_singleton_iff.mpr
          (congrArg Subtype.val (Set.mem_singleton_iff.mp hz))
    rw [heq]
    exact ((isClosed_singleton.preimage hm).isCompact.image hcont)

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : LocalizedCategory.{u, v, v} (K := K)} {f : X ⟶ Y}

set_option backward.isDefEq.respectTransparency false in
/-- An analytic closed immersion induces a closed embedding on underlying spaces. -/
theorem closedImmersion.isClosedEmbedding (hf : closedImmersion f) :
    IsClosedEmbedding (localizedSpaceFunctor.map f) := by
  obtain ⟨A, B, g, hg, ⟨e⟩⟩ := hf
  let ex : localizationFunctor.obj (ofSaturation A) ≅ X := Arrow.leftFunc.mapIso e
  let ey : localizationFunctor.obj (ofSaturation B) ≅ Y := Arrow.rightFunc.mapIso e
  have hw : ex.hom ≫ f = localizationFunctor.map g ≫ ey.hom := e.hom.w
  have he : f = ex.inv ≫ localizationFunctor.map g ≫ ey.hom := by rw [← hw]; simp
  have hg' : IsClosedEmbedding (localizedSpaceFunctor.map (localizationFunctor.map g)) :=
    IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.mpr
      ⟨g.baseMap.continuous, injective_of_strongClosedImmersion hg,
        hg.isFinite.isProperMap.isClosedMap⟩
  rw [he, Functor.map_comp, Functor.map_comp, TopCat.coe_comp, TopCat.coe_comp]
  exact ((TopCat.homeoOfIso (localizedSpaceFunctor.mapIso ey)).isClosedEmbedding.comp hg').comp
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso ex.symm)).isClosedEmbedding

/-- The underlying source of a closed immersion is homeomorphic to the
closed image with its subspace topology. -/
def closedImmersion.rangeHomeomorph (hf : closedImmersion f) :
    localizedSpaceFunctor.obj X ≃ₜ Set.range (localizedSpaceFunctor.map f) :=
  hf.isClosedEmbedding.isEmbedding.toHomeomorph

end Langlands.Analytic.SaturatedAtlasPresentation
