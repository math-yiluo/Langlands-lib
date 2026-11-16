import Langlands.Geometry.Analytic.FullRecognitionEtaleMorphisms

/-! # Pointed finite full-recognition chart pairs -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open Set Filter
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

/-- A finite full-recognition chart pair through the specified source point. -/
def HasFiniteFullRecognitionPairAt
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation) (y : A.space) : Prop :=
  ∃ (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' range V.chart ⊆ range W.chart)
    (s : BanachSpectrum V.algebra),
    V.chart s = y ∧ (g.fullRecognitionPairs.pullback V W h).IsFiniteBanach

/-- Select one of the finite chart pieces at the specified point, retaining
its pointwise property. -/
theorem HasFinitePiecesAt.exists_pointed_fullRecognitionPair
    {Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄,
      BoundedAlgHom K R S → BanachSpectrum S → Prop}
    {y : A.space} (hg : g.HasFinitePiecesAt Q y) :
    ∃ (V : A.atlas.saturatedAtlas.RecognizedSubset)
      (W : B.atlas.saturatedAtlas.RecognizedSubset)
      (h : g.baseMap '' range V.chart ⊆ range W.chart)
      (s : BanachSpectrum V.algebra),
      V.chart s = y ∧ (g.fullRecognitionPairs.pullback V W h).IsFiniteBanach ∧
        Q (g.fullRecognitionPairs.pullback V W h) s := by
  obtain ⟨V₀, U₀, -, -, hy, hfin, I, -, hIU, hIN, hIQ⟩ := hg
  obtain ⟨W, hW, hyW⟩ := Set.mem_iUnion₂.mp (mem_of_mem_nhds hIN)
  obtain ⟨V, h, hV, hf⟩ := hfin.2 W (hIU W hW).1
  have hyV : y ∈ range V.chart := by
    rw [V.range_chart, hV]
    exact ⟨hy, hyW⟩
  obtain ⟨s, hs⟩ := hyV
  exact ⟨V, W, h, s, hs, hf, hIQ W hW V h hV s hs⟩

/-- Finiteness at a point supplies an actual finite full-recognition chart
pair through that point. -/
theorem IsFiniteAt.hasFiniteFullRecognitionPairAt
    {y : A.space} (hg : g.IsFiniteAt y) : g.HasFiniteFullRecognitionPairAt y := by
  obtain ⟨V₀, U₀, hV₀, hU₀, hy, hfin⟩ := hg
  have hpieces : g.HasFinitePiecesAt (fun _ _ _ _ => True) y :=
    hasFinitePiecesAt_of_isFiniteOver hV₀ hU₀ hfin (fun _ _ _ _ _ _ => trivial) hy
  obtain ⟨V, W, h, s, hs, hf, -⟩ := hpieces.exists_pointed_fullRecognitionPair
  exact ⟨V, W, h, s, hs, hf⟩

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
