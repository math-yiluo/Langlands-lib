import Langlands.Geometry.Analytic.FullRecognitionPointedFinitePairs
import Langlands.Geometry.Analytic.FieldValuedPoints
import Langlands.Geometry.Analytic.Spectrum.ResidueField.CharacterTransport

/-! # Prescribed characters on finite full-recognition pairs -/

noncomputable section

universe u v w uL

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {L : Type uL} [NormedField L] [NormedAlgebra K L]
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

/-- A finite local chart pair through `y` carrying a character that realizes
`y` and restricts to the prescribed full-recognition field point. -/
def HasFiniteCharacterLiftAt
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation) (y : A.space)
    (p : FieldPoint L B.fullRecognitionPresentation) : Prop :=
  ∃ (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' range V.chart ⊆ range W.chart)
    (s : BanachSpectrum V.algebra) (hw : p.point ∈ range W.chart)
    (c : BoundedAlgHom K V.algebra L),
    V.chart s = y ∧ (g.fullRecognitionPairs.pullback V W h).IsFiniteBanach ∧
      (∀ b, ‖c b‖ = s b) ∧
        c.toAlgHom.comp (g.fullRecognitionPairs.pullback V W h).toAlgHom = p.eval W hw

/-- A prescribed target field point supplies a lift on a finite local chart
pair through every chosen source point where the morphism is finite. -/
theorem IsFiniteAt.hasFiniteCharacterLiftAt
    [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
    {y : A.space} (hg : g.IsFiniteAt y)
    (p : FieldPoint L B.fullRecognitionPresentation) (hp : p.point = g.baseMap y) :
    g.HasFiniteCharacterLiftAt y p := by
  obtain ⟨V, W, h, s, hs, hf⟩ := hg.hasFiniteFullRecognitionPairAt
  have hw : p.point ∈ range W.chart := hp.symm ▸ h ⟨y, ⟨s, hs⟩, rfl⟩
  obtain ⟨t, ht, hn⟩ := p.isChartPoint W hw
  have hc : W.chart
      (BanachSpectrum.comap (g.fullRecognitionPairs.pullback V W h).toBoundedRingHom s) =
      p.point :=
    (g.fullRecognitionPairs.chart_comm V W h s).trans
      ((congrArg g.baseMap hs).trans hp.symm)
  have ht' : t =
      BanachSpectrum.comap (g.fullRecognitionPairs.pullback V W h).toBoundedRingHom s :=
    (B.fullRecognitionPresentation.atlas.isEmbedding_chart W).injective
      (ht.trans hc.symm)
  obtain ⟨c, hcn, hcr⟩ := BanachSpectrum.exists_character_lift_of_finite K
    (g.fullRecognitionPairs.pullback V W h) hf.finite s (p.eval W hw)
    (fun a => (hn a).trans (congrArg (fun z : BanachSpectrum W.algebra => z a) ht'))
  refine ⟨V, W, h, s, hw, c, hs, hf, hcn, ?_⟩
  ext a
  exact hcr a

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
