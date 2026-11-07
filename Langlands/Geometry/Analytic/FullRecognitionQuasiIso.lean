import Langlands.Geometry.Analytic.QuasiIsoRecognizedNaturality
import Langlands.Geometry.Analytic.RecognizedDomainClosure

/-! # Actual quasi-isomorphism extension to full recognition atlases -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation

/-- Full recognition uses the original full local-domain net and retains
exactly the original ambient topological space. -/
def fullRecognitionPresentation (A : AffinoidAtlasPresentation.{u, v, w} K) :
    AffinoidAtlasPresentation.{u, v, v} K where
  space := A.space
  atlas := A.atlas.fullRecognitionAtlas

theorem fullRecognitionPresentation_hasAllLocalDomains
    (A : AffinoidAtlasPresentation.{u, v, w} K) :
    A.fullRecognitionPresentation.atlas.HasAllLocalDomains :=
  A.atlas.fullRecognitionAtlas_localDomainFamily

namespace StrongHom.IsQuasiIso

variable {A B : AffinoidAtlasPresentation.{u, v, w} K} {f : StrongHom A B}
  (hf : f.IsQuasiIso) (hc : f.HasCoherentPullbacks)

/-- Every admissible target recognized chart contains the actual recognized
image of the entire source chart. -/
theorem recognizedImage_subset_of_image_subset
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : f.baseMap '' V.locus ⊆ W.locus) :
    (hf.recognizedImage hc V).locus ⊆ W.locus := by
  rw [hf.recognizedImage_locus]
  exact h

/-- The whole bounded pullback to a source recognized chart is the
canonical target restriction followed by the constructed inverse comparison. -/
def fullRecognitionPullback
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : f.baseMap '' V.locus ⊆ W.locus) : BoundedAlgHom K W.algebra V.algebra :=
  (hf.recognizedImageEquiv hc V).symm.toBoundedAlgHom.comp
    ((hf.recognizedImage hc V).restriction W
      (hf.recognizedImage_subset_of_image_subset hc V W h))

theorem fullRecognitionPullback_chart
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : f.baseMap '' V.locus ⊆ W.locus) (x : BanachSpectrum V.algebra) :
    W.chart (BanachSpectrum.comap
      (hf.fullRecognitionPullback hc V W h).toBoundedRingHom x) =
        f.baseMap (V.chart x) := by
  let e := hf.recognizedImageEquiv hc V
  let Y := hf.recognizedImage hc V
  let r := Y.restriction W (hf.recognizedImage_subset_of_image_subset hc V W h)
  have hp : BanachSpectrum.comap
      (hf.fullRecognitionPullback hc V W h).toBoundedRingHom x =
      BanachSpectrum.comap r.toBoundedRingHom (e.spectrumHomeomorph.symm x) :=
    BanachSpectrum.ext fun _ => rfl
  exact (congrArg W.chart hp).trans
    ((Y.chart_restriction W _ (e.spectrumHomeomorph.symm x)).trans
      ((hf.recognizedImage_chart hc V (e.spectrumHomeomorph.symm x)).trans
        (congrArg (fun y => f.baseMap (V.chart y))
          (e.spectrumHomeomorph.apply_symm_apply x))))

/-- Full source and target restriction compatibility is an equality of
entire bounded maps, using the original forward comparison naturality. -/
theorem fullRecognitionPullback_naturality
    (U V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W Z : B.atlas.saturatedAtlas.RecognizedSubset)
    (hUV : U.locus ⊆ V.locus) (hWZ : W.locus ⊆ Z.locus)
    (hUW : f.baseMap '' U.locus ⊆ W.locus)
    (hVZ : f.baseMap '' V.locus ⊆ Z.locus) :
    (U.restriction V hUV).comp (hf.fullRecognitionPullback hc V Z hVZ) =
      (hf.fullRecognitionPullback hc U W hUW).comp (W.restriction Z hWZ) := by
  let Y := hf.recognizedImage hc U
  let T := hf.recognizedImage hc V
  let e := hf.recognizedImageEquiv hc U
  let d := hf.recognizedImageEquiv hc V
  have hYT : Y.locus ⊆ T.locus := by
    rw [hf.recognizedImage_locus, hf.recognizedImage_locus]
    exact Set.image_mono hUV
  let hYW := hf.recognizedImage_subset_of_image_subset hc U W hUW
  let hTZ := hf.recognizedImage_subset_of_image_subset hc V Z hVZ
  have hn := hf.recognizedImageEquiv_naturality hc U V hUV
  ext x
  apply e.injective
  have h₁ := congrArg (fun q : BoundedAlgHom K V.algebra Y.algebra =>
    q (d.symm (T.restriction Z hTZ x))) hn
  have h₂ := congrArg (fun q : BoundedAlgHom K Z.algebra Y.algebra => q x)
    (Y.restriction_comp T Z hYT hTZ)
  have h₃ := congrArg (fun q : BoundedAlgHom K Z.algebra Y.algebra => q x)
    (Y.restriction_comp W Z hYW hWZ)
  change e (U.restriction V hUV (d.symm (T.restriction Z hTZ x))) =
    e (e.symm (Y.restriction W hYW (W.restriction Z hWZ x)))
  rw [e.apply_symm_apply]
  exact h₁.trans ((congrArg (Y.restriction T hYT)
    (d.apply_symm_apply (T.restriction Z hTZ x))).trans (h₂.trans h₃.symm))

/-- Every supplied bounded pullback fully represents its literal relative
image domain, including all presented-affinoid coefficient tests. -/
theorem fullRecognitionPullback_represents
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : f.baseMap '' V.locus ⊆ W.locus) :
    Represents K (hf.fullRecognitionPullback hc V W h)
      (W.chart ⁻¹' (f.baseMap '' V.locus)) := by
  have hr := ((hf.recognizedImage hc V).restriction_represents W
    (hf.recognizedImage_subset_of_image_subset hc V W h)).postcomp_equiv
      (hf.recognizedImageEquiv hc V).symm
  rw [hf.recognizedImage_locus] at hr
  exact hr

/-- Construct the actual all-admissible-pair strong extension between full
recognition atlases. Neither original atlas needs full-domain closure. -/
def fullRecognitionExtension :
    StrongHom A.fullRecognitionPresentation B.fullRecognitionPresentation where
  baseMap := f.baseMap
  target_exists V := by
    change A.atlas.saturatedAtlas.RecognizedSubset at V
    refine ⟨hf.recognizedImage hc V, ?_⟩
    change f.baseMap '' Set.range V.chart ⊆ Set.range (hf.recognizedImage hc V).chart
    rw [V.range_chart, (hf.recognizedImage hc V).range_chart,
      hf.recognizedImage_locus]
  pullback V W h := hf.fullRecognitionPullback hc V W (by
    change A.atlas.saturatedAtlas.RecognizedSubset at V
    change B.atlas.saturatedAtlas.RecognizedSubset at W
    change f.baseMap '' Set.range V.chart ⊆ Set.range W.chart at h
    simpa only [V.range_chart, W.range_chart] using h)
  chart_comm V W h x := hf.fullRecognitionPullback_chart hc V W _ x
  restriction_comm U V W Z hUV hWZ hUW hVZ := by
    change A.atlas.saturatedAtlas.RecognizedSubset at U V
    change B.atlas.saturatedAtlas.RecognizedSubset at W Z
    change Set.range U.chart ⊆ Set.range V.chart at hUV
    change Set.range W.chart ⊆ Set.range Z.chart at hWZ
    exact hf.fullRecognitionPullback_naturality hc U V W Z
      (by simpa only [U.range_chart, V.range_chart] using hUV)
      (by simpa only [W.range_chart, Z.range_chart] using hWZ) _ _

@[simp]
theorem fullRecognitionExtension_baseMap :
    (hf.fullRecognitionExtension hc).baseMap = f.baseMap := rfl

/-- The extension is a genuine strong quasi-isomorphism on every
admissible recognized chart pair, rather than only on chosen pairs. -/
theorem fullRecognitionExtension_isQuasiIso :
    (hf.fullRecognitionExtension hc).IsQuasiIso := by
  refine ⟨hf.1, ?_⟩
  intro V W h
  change A.atlas.saturatedAtlas.RecognizedSubset at V
  change B.atlas.saturatedAtlas.RecognizedSubset at W
  change f.baseMap '' Set.range V.chart ⊆ Set.range W.chart at h
  have hlocus : f.baseMap '' V.locus ⊆ W.locus := by
    simpa only [V.range_chart, W.range_chart] using h
  change Represents K (hf.fullRecognitionPullback hc V W hlocus)
    (W.chart ⁻¹' (f.baseMap '' Set.range V.chart))
  rw [V.range_chart]
  exact hf.fullRecognitionPullback_represents hc V W _

/-- Closure of the constructed source full atlas discharges intrinsic
coherence, with no further premise on either original presentation. -/
theorem fullRecognitionExtension_hasCoherentPullbacks :
    (hf.fullRecognitionExtension hc).HasCoherentPullbacks :=
  (hf.fullRecognitionExtension hc).hasCoherentPullbacks_of_saturated
    A.fullRecognitionPresentation_hasAllLocalDomains

end StrongHom.IsQuasiIso
end AffinoidAtlasPresentation
end Langlands.Analytic
