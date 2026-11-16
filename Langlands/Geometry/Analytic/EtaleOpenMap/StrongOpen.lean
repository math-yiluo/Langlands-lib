import Langlands.Geometry.Analytic.EtaleOpenMap.FiniteFlatImage
import Langlands.Geometry.Analytic.FullRecognitionEtaleComposition

/-! # Openness of strong analytic maps which are flat over all pieces -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

/-- Shrinking a finite neighborhood keeps flatness at the distinguished point:
the smaller affinoid pieces are clopen pieces of the old ones. -/
theorem IsFlatAtAllPieces.exists_small {y : A.space} (hg : g.IsFlatAtAllPieces y)
    {O : Set A.space} (hO : O ∈ 𝓝 y) :
    ∃ (V : Set A.space) (U : Set B.space), IsOpen V ∧ IsOpen U ∧ y ∈ V ∧ V ⊆ O ∧
      g.IsFiniteOver V U ∧
      ∀ W : B.atlas.saturatedAtlas.RecognizedSubset, W.locus ⊆ U → g.baseMap y ∈ W.locus →
        ∀ (P : A.atlas.saturatedAtlas.RecognizedSubset)
          (h : g.baseMap '' Set.range P.chart ⊆ Set.range W.chart),
          P.locus = V ∩ g.baseMap ⁻¹' W.locus →
            ∀ s : BanachSpectrum P.algebra, P.chart s = y →
              (g.fullRecognitionPairs.pullback P W h).IsFlatAtPoint s := by
  obtain ⟨V₀, U₀, hV₀, hU₀, hy, hfin₀, hflat₀⟩ := hg
  obtain ⟨V, U, hV, hU, hyV, hVO, hVV₀, hUU₀, hfin⟩ := hfin₀.exists_small hV₀ hU₀ hy hO
  refine ⟨V, U, hV, hU, hyV, hVO, hfin, ?_⟩
  intro W hWU hxW P h hP s hs
  obtain ⟨P₀, h₀, hP₀, -⟩ := hfin₀.2 W (hWU.trans hUU₀)
  have hPP₀ : P.locus = P₀.locus ∩ V := by
    rw [hP, hP₀]
    ext p
    constructor
    · rintro ⟨hpV, hpW⟩
      exact ⟨⟨hVV₀ hpV, hpW⟩, hpV⟩
    · rintro ⟨⟨-, hpW⟩, hpV⟩
      exact ⟨hpV, hpW⟩
  have hsub : P.locus ⊆ P₀.locus := hPP₀.trans_subset Set.inter_subset_left
  have hcl := P.isClopen_chart_preimage_of_eq_inter P₀ hV hPP₀
  have hrflat := (P.restriction_flat_and_surjective P₀ hsub hcl).1
  have hPr : Set.range P.chart ⊆ Set.range P₀.chart := by
    rw [P.range_chart, P₀.range_chart]
    exact hsub
  have hcomm := g.fullRecognitionPairs.restriction_comm P P₀ W W hPr
    (Set.Subset.refl _) h h₀
  rw [B.fullRecognitionPresentation.atlas.restriction_id W (Set.Subset.refl _),
    BoundedAlgHom.comp_id] at hcomm
  rw [← hcomm]
  refine ((P.restriction P₀ hsub).isFlatAtPoint_of_flat hrflat s).comp ?_
  exact hflat₀ W (hWU.trans hUU₀) hxW P₀ h₀ hP₀ _
    ((P.chart_restriction P₀ hsub s).trans hs)

/-- The image of every neighborhood of a flat point over all pieces is a
neighborhood of its image. -/
theorem IsFlatAtAllPieces.image_mem_nhds {y : A.space} (hg : g.IsFlatAtAllPieces y)
    {O : Set A.space} (hO : O ∈ 𝓝 y) : g.baseMap '' O ∈ 𝓝 (g.baseMap y) := by
  obtain ⟨V, U, hV, hU, hyV, hVO, hfin, hflat⟩ := hg.exists_small hO
  have hxU : g.baseMap y ∈ U := hfin.1 ⟨y, hyV, rfl⟩
  obtain ⟨I, hI, hIU, hIN⟩ :=
    B.atlas.exists_finite_recognized_nhds_subset (g.baseMap y) U (hU.mem_nhds hxU)
  have hlocal : ∀ W ∈ I, ∃ N ∈ 𝓝 (g.baseMap y), N ∩ W.locus ⊆ g.baseMap '' O := by
    intro W hWI
    obtain ⟨P, h, hP, hPfin⟩ := hfin.2 W (hIU W hWI).2
    have hyP : y ∈ P.locus := hP ▸ ⟨hyV, (hIU W hWI).1⟩
    obtain ⟨s, hs⟩ := (P.range_chart ▸ hyP : y ∈ Set.range P.chart)
    let f : BoundedAlgHom K W.algebra P.algebra := g.fullRecognitionPairs.pullback P W h
    let t : BanachSpectrum W.algebra := BanachSpectrum.comap f.toBoundedRingHom s
    have ht : W.chart t = g.baseMap y :=
      (g.fullRecognitionPairs.chart_comm P W h s).trans (congrArg g.baseMap hs)
    have hflat' : f.IsFlatAtPoint s := hflat W (hIU W hWI).2 (hIU W hWI).1 P h hP s hs
    have hn : Set.range (BanachSpectrum.comap f.toBoundedRingHom) ∈ 𝓝 t :=
      hflat'.range_comap_mem_nhds hPfin
    have he : 𝓝 t = Filter.comap W.chart (𝓝 (W.chart t)) :=
      W.isEmbedding_chart.nhds_eq_comap t
    rw [he, ht, Filter.mem_comap] at hn
    obtain ⟨N, hN, hNr⟩ := hn
    refine ⟨N, hN, ?_⟩
    rintro x ⟨hxN, hxW⟩
    obtain ⟨t', ht'⟩ := (W.range_chart ▸ hxW : x ∈ Set.range W.chart)
    obtain ⟨s', hs'⟩ := hNr (show W.chart t' ∈ N from ht' ▸ hxN)
    refine ⟨P.chart s', hVO ?_, ?_⟩
    · have hmem : P.chart s' ∈ P.locus := P.range_chart ▸ Set.mem_range_self s'
      rw [hP] at hmem
      exact hmem.1
    · have hc := g.fullRecognitionPairs.chart_comm P W h s'
      exact hc.symm.trans ((congrArg W.chart hs').trans ht')
  choose N hN hNsub using hlocal
  have hT : ⋂₀ {N' | ∃ W hW, N W hW = N'} ∈ 𝓝 (g.baseMap y) := by
    apply (Filter.sInter_mem (hI.dependent_image N)).2
    rintro _ ⟨W, hW, rfl⟩
    exact hN W hW
  refine Filter.mem_of_superset (Filter.inter_mem hIN hT) ?_
  rintro x ⟨hxI, hxT⟩
  obtain ⟨W, hWI, hxW⟩ := Set.mem_iUnion₂.1 hxI
  exact hNsub W hWI ⟨hxT _ ⟨W, hWI, rfl⟩, hxW⟩

/-- A strong analytic map flat over all affinoid pieces at every point is open. -/
theorem isOpenMap_of_isFlatAtAllPieces (hg : ∀ y, g.IsFlatAtAllPieces y) :
    IsOpenMap g.baseMap := by
  intro O hO
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨y, hy, rfl⟩
  exact (hg y).image_mem_nhds (hO.mem_nhds hy)

/-- Strong étale maps are open on their actual underlying spaces. -/
theorem IsEtaleAllPieces.isOpenMap (hg : g.IsEtaleAllPieces) : IsOpenMap g.baseMap := by
  apply isOpenMap_of_isFlatAtAllPieces
  intro y
  obtain ⟨V, -, hy, hV⟩ := hg y
  exact (hV y hy).2

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
