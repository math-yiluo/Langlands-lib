import Langlands.Geometry.Analytic.QuasiIsoFiniteEtale
import Langlands.Geometry.Analytic.SaturatedLocalizedFractions

/-! # Transport of étaleness across full quasi-isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.StrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- A full quasi-isomorphism between constructed saturations is finite
étale for its actual full-recognition pair system. -/
theorem IsQuasiIso.isFiniteEtale
    {g : StrongHom A.saturatedPresentation B.saturatedPresentation}
    (hg : g.IsQuasiIso) : g.IsFiniteEtale := by
  have h := hg.originalRestriction.saturationExtension_isFiniteEtale
    g.originalRestriction.coherent
  change g.originalRestriction.saturationExtension.IsFiniteEtale at h
  simpa only [g.saturationExtension_originalRestriction] using h

/-- Such denominators are étale over every recognized affinoid piece. -/
theorem IsQuasiIso.isEtaleAllPieces
    {g : StrongHom A.saturatedPresentation B.saturatedPresentation}
    (hg : g.IsQuasiIso) : g.IsEtaleAllPieces :=
  hg.isFiniteEtale.isEtaleAllPieces

/-- The actual pair-system map of a full quasi-isomorphism represents
its relative image over every recognized target chart. -/
theorem IsQuasiIso.fullRecognitionPairs_represents
    {g : StrongHom A.saturatedPresentation B.saturatedPresentation}
    (hg : g.IsQuasiIso)
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' Set.range V.chart ⊆ Set.range W.chart)
    (hl : g.baseMap '' V.locus ⊆ W.locus) :
    Represents K (g.fullRecognitionPairs.pullback V W h)
      (W.chart ⁻¹' (g.baseMap '' V.locus)) := by
  have hp := hg.originalRestriction.saturationExtension_fullRecognitionPairs_represents
    g.originalRestriction.coherent V W h hl
  change Represents K
    (g.originalRestriction.saturationExtension.fullRecognitionPairs.pullback V W h)
    (W.chart ⁻¹' (g.baseMap '' V.locus)) at hp
  simpa only [g.saturationExtension_originalRestriction] using hp

/-- Full-image recognized pairs of any full quasi-isomorphism between
constructed saturations carry an actual bounded algebra equivalence. -/
def IsQuasiIso.fullRecognitionPairEquiv
    {g : StrongHom A.saturatedPresentation B.saturatedPresentation}
    (hg : g.IsQuasiIso)
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' Set.range V.chart ⊆ Set.range W.chart)
    (hl : g.baseMap '' V.locus ⊆ W.locus)
    (hu : W.chart ⁻¹' (g.baseMap '' V.locus) = Set.univ) :
    BoundedAlgEquiv K W.algebra V.algebra :=
  ((congrArg (fun s => Represents K
    (g.fullRecognitionPairs.pullback V W h) s) hu).mp
      (hg.fullRecognitionPairs_represents V W h hl)).univEquiv

/-- This equivalence retains the complete actual pair-system pullback. -/
theorem IsQuasiIso.fullRecognitionPairEquiv_toBoundedAlgHom
    {g : StrongHom A.saturatedPresentation B.saturatedPresentation}
    (hg : g.IsQuasiIso)
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' Set.range V.chart ⊆ Set.range W.chart)
    (hl : g.baseMap '' V.locus ⊆ W.locus)
    (hu : W.chart ⁻¹' (g.baseMap '' V.locus) = Set.univ) :
    (hg.fullRecognitionPairEquiv V W h hl hu).toBoundedAlgHom =
      g.fullRecognitionPairs.pullback V W h :=
  Represents.univEquiv_toBoundedAlgHom _

/-- Full quasi-isomorphisms cancel on the right of saturated composition. -/
theorem IsQuasiIso.of_saturatedComp_right
    {f : StrongHom A B} {g : StrongHom B C}
    (hg : g.IsQuasiIso)
    (ha : A.atlas.HasAllLocalDomains) (hb : B.atlas.HasAllLocalDomains)
    (hfg : (f.saturatedComp g ha hb).IsQuasiIso) : f.IsQuasiIso := by
  have heq : hg.1.homeomorph.symm ∘ (f.saturatedComp g ha hb).baseMap =
      f.baseMap := by
    funext x
    exact hg.1.homeomorph.symm_apply_apply (f.baseMap x)
  refine ⟨heq ▸ (hg.1.homeomorph.symm.isHomeomorph.comp hfg.1), ?_⟩
  intro i j hf
  obtain ⟨k, hgk⟩ := g.target_exists j
  let hcomp := f.comp_admissible g i j k hf hgk
  have h := hfg.2 i k hcomp
  rw [saturatedComp_pullback f g ha hb i j k hf hgk hcomp] at h
  have hr := (hg.2 j k hgk).of_comp_of_injective h
    (hg.isEmbedding_pullback j k hgk).injective
  have hl : (BanachSpectrum.comap (g.pullback j k hgk).toBoundedRingHom) ⁻¹'
      (f.saturatedComp g ha hb).chartImageLocus i k = f.chartImageLocus i j := by
    ext x
    change C.atlas.chart k (BanachSpectrum.comap
      (g.pullback j k hgk).toBoundedRingHom x) ∈
        (g.baseMap.comp f.baseMap) '' Set.range (A.atlas.chart i) ↔
      B.atlas.chart j x ∈ f.baseMap '' Set.range (A.atlas.chart i)
    rw [g.chart_comm]
    constructor
    · rintro ⟨z, hz, he⟩
      exact ⟨z, hz, hg.1.injective he⟩
    · rintro ⟨z, hz, he⟩
      exact ⟨z, hz, congrArg g.baseMap he⟩
  exact (congrArg (Represents K (f.pullback i j hf)) hl).mp hr

end AffinoidAtlasPresentation.StrongHom
end Langlands.Analytic
