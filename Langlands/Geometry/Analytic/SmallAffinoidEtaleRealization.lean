import Langlands.Geometry.Analytic.RecognizedPointwiseEtale
import Langlands.Geometry.Analytic.SmallAffinoidPointwiseSquare
import Langlands.Geometry.Analytic.SaturatedEtaleComparison

/-! # Finite pointwise étale maps of small actual affinoid spectra -/

noncomputable section

universe u v

namespace Langlands.Analytic.SmallAffinoidSpectrum

open CategoryTheory Set PresentedAffinoidAlgebra AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The global original affinoid chart retained in the first saturation. -/
def globalChart (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)] :
    (saturated R).presentation.atlas.Index :=
  (presentation R).atlas.originalSaturatedIndex PUnit.unit

theorem globalChart_range (R : PresentedAffinoidAlgebra K)
    [Small.{v} (BanachSpectrum R)] :
    range ((saturated R).presentation.atlas.chart (globalChart R)) = univ :=
  ((presentation R).atlas.saturatedAtlas_original_range PUnit.unit).trans
    (spectrumHomeomorph R).surjective.range_eq

theorem globalChart_algebra (R : PresentedAffinoidAlgebra K)
    [Small.{v} (BanachSpectrum R)] :
    (saturated R).presentation.atlas.algebra (globalChart R) = R :=
  (presentation R).atlas.saturatedAtlas_original_algebra PUnit.unit

/-- The same global chart retained in the canonical second saturation. -/
def canonicalGlobalChart (R : PresentedAffinoidAlgebra K)
    [Small.{v} (BanachSpectrum R)] :
    (saturated R).presentation.atlas.saturatedAtlas.Index :=
  (saturated R).presentation.atlas.originalSaturatedIndex (globalChart R)

theorem canonicalGlobalChart_range (R : PresentedAffinoidAlgebra K)
    [Small.{v} (BanachSpectrum R)] :
    range ((saturated R).presentation.atlas.saturatedAtlas.chart
      (canonicalGlobalChart R)) = univ :=
  ((saturated R).presentation.atlas.saturatedAtlas_original_range (globalChart R)).trans
    (globalChart_range R)

theorem canonicalGlobalChart_algebra (R : PresentedAffinoidAlgebra K)
    [Small.{v} (BanachSpectrum R)] :
    (saturated R).presentation.atlas.saturatedAtlas.algebra
      (canonicalGlobalChart R) = R :=
  ((saturated R).presentation.atlas.saturatedAtlas_original_algebra (globalChart R)).trans
    (globalChart_algebra R)

variable {R S : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]
    (f : BoundedAlgHom K R S)

/-- The actual canonical saturation extension tested by `strongEtale`. -/
def canonicalMap :
    StrongHom (saturated S).presentation.saturatedPresentation
      (saturated R).presentation.saturatedPresentation :=
  ((SaturatedAtlasPresentation.compatibleFunctor ⋙
    CompatibleAtlasPresentation.saturationFunctor).map (map f))

theorem globalChart_admissible :
    (map f).baseMap '' range ((saturated S).presentation.atlas.chart (globalChart S)) ⊆
      range ((saturated R).presentation.atlas.chart (globalChart R)) := by
  rw [globalChart_range R]
  exact subset_univ _

theorem canonicalGlobalChart_admissible :
    (canonicalMap f).baseMap ''
      range ((saturated S).presentation.atlas.saturatedAtlas.chart (canonicalGlobalChart S)) ⊆
      range ((saturated R).presentation.atlas.saturatedAtlas.chart (canonicalGlobalChart R)) :=
  (subset_univ _).trans (canonicalGlobalChart_range R).symm.subset

/-- Recovery on both original chart inclusions retains the full bounded map. -/
theorem canonicalMap_pullback_global_heq :
    HEq ((canonicalMap f).pullback (canonicalGlobalChart S) (canonicalGlobalChart R)
      (canonicalGlobalChart_admissible f)) f := by
  have h₀ : (strongMap f).baseMap '' range ((presentation S).atlas.chart PUnit.unit) ⊆
      range ((presentation R).atlas.chart PUnit.unit) := by
    change (strongMap f).baseMap '' range (spectrumHomeomorph S) ⊆
      range (spectrumHomeomorph R)
    rw [(spectrumHomeomorph R).surjective.range_eq]
    exact subset_univ _
  have h₁ := (strongMap f).saturationExtension_pullback_original
    (strongMap_coherent f) PUnit.unit PUnit.unit h₀
  have h₂ := (map f).saturationExtension_pullback_original
    ((map f).hasCoherentPullbacks_of_saturated (saturated S).hasAllLocalDomains)
    (globalChart S) (globalChart R) (globalChart_admissible f)
  exact h₂.trans h₁

omit [CompleteSpace K] [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)] in
private theorem finitePointwiseEtale_of_heq
    {R' S' : PresentedAffinoidAlgebra K} (hR : R' = R) (hS : S' = S)
    {f' : BoundedAlgHom K R' S'} (he : HEq f' f)
    (hf : f.IsFiniteBanach) (het : ∀ s, f.IsEtaleAtPoint s) :
    f'.IsFiniteBanach ∧ ∀ s, f'.IsEtaleAtPoint s := by
  cases hR
  cases hS
  cases eq_of_heq he
  exact ⟨hf, het⟩

/-- A finite Banach bounded map étale at every ordinary spectrum point yields
the canonical strong étale map in any supplied small space universe. -/
theorem map_strongEtale_of_finite_pointwiseEtale
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (hf : f.IsFiniteBanach) (het : ∀ s, f.IsEtaleAtPoint s) :
    SaturatedAtlasPresentation.strongEtale (map f) := by
  have hp := finitePointwiseEtale_of_heq f
    (canonicalGlobalChart_algebra R) (canonicalGlobalChart_algebra S)
    (canonicalMap_pullback_global_heq f) hf het
  exact (canonicalMap f).isEtaleAllPieces_of_globalCharts
    (canonicalGlobalChart S) (canonicalGlobalChart R) (canonicalGlobalChart_admissible f)
    hpush htensor (canonicalGlobalChart_range S) (canonicalGlobalChart_range R) hp.1 hp.2

/-- This is étaleness for the actual localized category used by the site. -/
theorem map_etale_of_finite_pointwiseEtale
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (hf : f.IsFiniteBanach) (het : ∀ s, f.IsEtaleAtPoint s) :
    SaturatedAtlasPresentation.etale
      (SaturatedAtlasPresentation.localizationFunctor.map (map f)) :=
  SaturatedAtlasPresentation.etale_map_of_strongEtale (map f)
    (map_strongEtale_of_finite_pointwiseEtale f hpush htensor hf het)

end Langlands.Analytic.SmallAffinoidSpectrum
