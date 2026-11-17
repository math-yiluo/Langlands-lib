import Langlands.Geometry.Analytic.FinitePiecesEtaleAllPiecesStatement
import Langlands.Geometry.Analytic.RecognizedNestedEtale
import Langlands.Geometry.Analytic.AffinoidProductChartSystem

/-! # Finite-to-all transport reduced to full-domain flatness and tensor comparison -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The actual finite-to-all conclusion follows from algebraic flatness of
full domains and ordinary tensor comparison for finite Banach maps. -/
theorem finitePiecesEtaleAllPieces_of_flatness_tensor
    (hflat : Domain.FlatnessStatement.{u})
    (hcomp : AffinoidPushout.FiniteTensorComparisonStatement K) :
    FinitePiecesEtaleAllPiecesStatement.{u, v, w} K := by
  intro A B g y hg
  obtain ⟨V, U, hV, hU, hy, hfin, I, hIfin, hIU, hIN, hIQ⟩ := hg
  obtain ⟨W₀, hW₀I, hxW₀⟩ := Set.mem_iUnion₂.mp (mem_of_mem_nhds hIN)
  obtain ⟨P₀, h₀, hP₀, hf₀⟩ := hfin.2 W₀ (hIU W₀ hW₀I).1
  refine ⟨V, U, hV, hU, hy, hfin, ?_⟩
  intro W hWU hxW P h hP s hs
  obtain ⟨P', h', hP', hf'⟩ := hfin.2 W hWU
  have hPP' : P = P' := Subtype.ext (Subtype.ext (hP.trans hP'.symm))
  have hf : (g.fullRecognitionPairs.pullback P W h).IsFiniteBanach := by
    subst hPP'
    exact hf'
  have hxW₀' : g.baseMap y ∈ range (B.atlas.fullRecognitionAtlas.chart W₀) :=
    W₀.range_chart.symm ▸ hxW₀
  have hxW' : g.baseMap y ∈ range (B.atlas.fullRecognitionAtlas.chart W) :=
    W.range_chart.symm ▸ hxW
  obtain ⟨Z, hZsub, hxZ⟩ :=
    IndexedAffinoidAtlas.exists_chart_inter
      (a := B.atlas.fullRecognitionAtlas) hxW₀' hxW'
  change B.atlas.saturatedAtlas.RecognizedSubset at Z
  change range Z.chart ⊆ range W₀.chart ∩ range W.chart at hZsub
  change g.baseMap y ∈ range Z.chart at hxZ
  rw [Z.range_chart, W₀.range_chart, W.range_chart] at hZsub
  rw [Z.range_chart] at hxZ
  have hZW₀ : Z.locus ⊆ W₀.locus := hZsub.trans inter_subset_left
  have hZW : Z.locus ⊆ W.locus := hZsub.trans inter_subset_right
  obtain ⟨R, hR, hRpre, -⟩ := hfin.2 Z (hZW.trans hWU)
  have hRP₀ : R.locus ⊆ P₀.locus := by
    rw [hRpre, hP₀]
    exact fun _ hz => ⟨hz.1, hZW₀ hz.2⟩
  have hRP : R.locus ⊆ P.locus := by
    rw [hRpre, hP]
    exact fun _ hz => ⟨hz.1, hZW hz.2⟩
  have hR₀ : R.locus = P₀.locus ∩ g.baseMap ⁻¹' Z.locus := by
    rw [hRpre, hP₀]
    ext z
    exact ⟨fun hz => ⟨⟨hz.1, hZW₀ hz.2⟩, hz.2⟩,
      fun hz => ⟨hz.1.1, hz.2⟩⟩
  have hRP' : R.locus = P.locus ∩ g.baseMap ⁻¹' Z.locus := by
    rw [hRpre, hP]
    ext z
    exact ⟨fun hz => ⟨⟨hz.1, hZW hz.2⟩, hz.2⟩,
      fun hz => ⟨hz.1.1, hz.2⟩⟩
  have hyR : y ∈ range R.chart := by
    rw [R.range_chart, hRpre]
    exact ⟨hy, hxZ⟩
  obtain ⟨t, ht⟩ := hyR
  have ht₀ : P₀.chart
      (BanachSpectrum.comap (R.restriction P₀ hRP₀).toBoundedRingHom t) = y :=
    (R.chart_restriction P₀ hRP₀ t).trans ht
  have het₀ := hIQ W₀ hW₀I P₀ h₀ hP₀ _ ht₀
  have hetR := (g.recognizedNested_isEtaleAtPoint_iff hflat hcomp
    P₀ R W₀ Z h₀ hR hZW₀ hRP₀ hR₀ hf₀ t).mpr het₀
  have hetP := (g.recognizedNested_isEtaleAtPoint_iff hflat hcomp
    P R W Z h hR hZW hRP hRP' hf t).mp hetR
  have hts : BanachSpectrum.comap (R.restriction P hRP).toBoundedRingHom t = s := by
    apply P.isEmbedding_chart.injective
    exact (R.chart_restriction P hRP t).trans (ht.trans hs.symm)
  exact (congrArg (fun z : BanachSpectrum P.algebra =>
    (g.fullRecognitionPairs.pullback P W h).IsEtaleAtPoint z) hts).mp hetP

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
