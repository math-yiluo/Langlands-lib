import Langlands.Geometry.Analytic.FiniteEtaleOverRecognition
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalLaurentNeighborhoods
import Langlands.Geometry.Analytic.SaturatedChartCoverRefinement

/-! # Finite étale refinements on affinoid charts -/

noncomputable section

universe u v w i

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

/-- Over a chart through the image point, a strong étale map contains a
finite étale surjection onto a subchart neighborhood. The source piece can
be confined to any ambient neighborhood of the chosen point. -/
theorem IsEtaleAllPieces.exists_surjective_finiteEtalePair
    (he : g.IsEtaleAllPieces) (y : A.space) (j : B.atlas.saturatedAtlas.Index)
    (x : BanachSpectrum (B.atlas.saturatedAtlas.algebra j))
    (hx : B.atlas.saturatedAtlas.chart j x = g.baseMap y)
    {N : Set A.space} (hN : N ∈ 𝓝 y) :
    ∃ (k : B.atlas.saturatedAtlas.Index) (P : A.atlas.saturatedAtlas.RecognizedSubset)
      (h : g.baseMap '' range P.chart ⊆ range (B.atlas.saturatedAtlas.originalRecognitionIndex k).chart),
      let W := B.atlas.saturatedAtlas.originalRecognitionIndex k
      y ∈ P.locus ∧ P.locus ⊆ N ∧
      W.locus ⊆ range (B.atlas.saturatedAtlas.chart j) ∧
      B.atlas.saturatedAtlas.chart j ⁻¹' W.locus ∈ 𝓝 x ∧
      (g.fullRecognitionPairs.pullback P W h).IsFiniteBanach ∧
      (g.fullRecognitionPairs.pullback P W h).AlgebraicallyFiniteEtale ∧
      Function.Surjective
        (BanachSpectrum.comap (g.fullRecognitionPairs.pullback P W h).toBoundedRingHom) := by
  obtain ⟨O, -, hyO, hO⟩ := he y
  obtain ⟨V, U, hV, -, hyV, hVN, hf, -⟩ := (hO y hyO).2.exists_small hN
  have hf' := he.isFiniteEtaleOver hV hf
  have hVim : g.baseMap '' V ∈ 𝓝 (g.baseMap y) :=
    (he.isOpenMap V hV).mem_nhds ⟨y, hyV, rfl⟩
  let a := B.atlas.saturatedAtlas
  have hpre : a.chart j ⁻¹' (g.baseMap '' V) ∈ 𝓝 x :=
    (a.isEmbedding_chart j).continuous.continuousAt.preimage_mem_nhds (hx.symm ▸ hVim)
  obtain ⟨d, hd, hsub⟩ := RationalChart.exists_rational_neighborhood x _ hpre
  let ha := B.atlas.saturatedAtlas_hasAllLocalDomains
  let k := ha.domainChartIndex j d.toDomain
  let W := a.originalRecognitionIndex k
  have hW : W.locus = a.chart j '' d.locus :=
    (show W.locus = range (a.chart k) from rfl).trans (ha.range_domainChartIndex j d.toDomain)
  have hWim : W.locus ⊆ g.baseMap '' V := by
    rw [hW]
    rintro _ ⟨s, hs, rfl⟩
    exact hsub hs
  have hWn : a.chart j ⁻¹' W.locus ∈ 𝓝 x := by
    rw [hW, preimage_image_eq _ (a.isEmbedding_chart j).injective]
    exact hd
  obtain ⟨P, h, hP, hfin, het⟩ := hf'.2 W (hWim.trans hf'.1)
  have hx' : x ∈ a.chart j ⁻¹' W.locus := mem_of_mem_nhds hWn
  have hxW : g.baseMap y ∈ W.locus := hx ▸ hx'
  refine ⟨k, P, h, ?_, ?_, ?_, hWn, hfin, het, ?_⟩
  · rw [hP]
    exact ⟨hyV, hxW⟩
  · exact (hP.trans_subset inter_subset_left).trans hVN
  · rw [hW]
    exact image_subset_range _ _
  · intro t
    have ht : W.chart t ∈ W.locus := W.range_chart ▸ mem_range_self t
    obtain ⟨z, hzV, hz⟩ := hWim ht
    have hzP : z ∈ range P.chart := by
      rw [P.range_chart, hP]
      exact ⟨hzV, show g.baseMap z ∈ W.locus from hz.symm ▸ ht⟩
    obtain ⟨s, hs⟩ := hzP
    refine ⟨s, W.isEmbedding_chart.injective ?_⟩
    exact (g.fullRecognitionPairs.chart_comm P W h s).trans ((congrArg g.baseMap hs).trans hz)

/-- Each base chart of a jointly surjective family of strong étale maps
has a finite cover by subcharts with spectrum-surjective finite étale maps
from actual recognized pieces of members of the family. -/
def StrongEtaleFiniteChartRefinementStatement (K : Type u)
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ {ι : Type i} (B : AffinoidAtlasPresentation.{u, v, w} K)
    (A : ι → AffinoidAtlasPresentation.{u, v, w} K)
    (e : ∀ b, StrongHom (A b).saturatedPresentation B.saturatedPresentation),
    (∀ b, (e b).IsEtaleAllPieces) →
    (∀ y : B.space, ∃ b z, (e b).baseMap z = y) →
    ∀ j : B.atlas.saturatedAtlas.Index,
      ∃ (n : ℕ) (b : Fin n → ι) (k : Fin n → B.atlas.saturatedAtlas.Index)
        (P : ∀ t, (A (b t)).atlas.saturatedAtlas.RecognizedSubset),
        let W := fun t => B.atlas.saturatedAtlas.originalRecognitionIndex (k t)
        ∃ h : ∀ t, (e (b t)).baseMap '' range (P t).chart ⊆ range (W t).chart,
          (∀ t, (W t).locus ⊆ range (B.atlas.saturatedAtlas.chart j)) ∧
          (range (B.atlas.saturatedAtlas.chart j) ⊆ ⋃ t, (W t).locus) ∧
          ∀ t, ((e (b t)).fullRecognitionPairs.pullback (P t) (W t) (h t)).IsFiniteBanach ∧
            ((e (b t)).fullRecognitionPairs.pullback (P t) (W t) (h t)).AlgebraicallyFiniteEtale ∧
            Function.Surjective (BanachSpectrum.comap
              ((e (b t)).fullRecognitionPairs.pullback (P t) (W t) (h t)).toBoundedRingHom)

theorem strongEtaleFiniteChartRefinement :
    StrongEtaleFiniteChartRefinementStatement.{u, v, w, i} K := by
  classical
  intro ι B A e he hcov j
  let a := B.atlas.saturatedAtlas
  choose b z hz using fun x : BanachSpectrum (a.algebra j) => hcov (a.chart j x)
  choose k P h _ _ hsub hn hf het hs using fun x =>
    (he (b x)).exists_surjective_finiteEtalePair (z x) j x (hz x).symm univ_mem
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover
    (fun x => a.chart j ⁻¹' (a.originalRecognitionIndex (k x)).locus) hn
  let idx := (Fintype.equivFin {x // x ∈ t}).symm
  refine ⟨Fintype.card {x // x ∈ t}, fun s => b (idx s).val, fun s => k (idx s).val,
    fun s => P (idx s).val, fun s => h (idx s).val, fun s => hsub (idx s).val, ?_,
    fun s => ⟨hf (idx s).val, het (idx s).val, hs (idx s).val⟩⟩
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ ⋃ y ∈ t, a.chart j ⁻¹' (a.originalRecognitionIndex (k y)).locus := by
    rw [ht]
    exact mem_univ x
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
  refine mem_iUnion.mpr ⟨idx.symm ⟨y, hy⟩, ?_⟩
  change a.chart j x ∈ (a.originalRecognitionIndex (k (idx (idx.symm ⟨y, hy⟩)).val)).locus
  rw [idx.apply_symm_apply]
  exact hxy

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
