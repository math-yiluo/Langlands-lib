import Langlands.Geometry.Analytic.TopChartAffinoidComparison
import Langlands.Geometry.Analytic.CompatibleDomainRestriction

/-! # Complete original compatible maps from a greatest source chart -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.CompatibleStrongHom

open Set CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (P : TopChartPresentation.{u, v, w} K) (hP : P.presentation.atlas.HasAllLocalDomains)
  {B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- An original compatible map from a greatest-chart source to one actual
target chart, followed by the compatible original-domain inclusion. -/
def fromChartPullback (j : B.atlas.Index)
    (φ : BoundedAlgHom K (B.atlas.algebra j) (P.presentation.atlas.algebra P.topChart)) :
    CompatibleStrongHom P.presentation B :=
  (CompatibleStrongHom.ofSaturated
    (TopChartPresentation.ofTopPullback (A := P) (B := TopChartPresentation.ofChart B j) φ) hP).comp
      (B.subspaceCompatibleInclusion (range (B.atlas.chart j)) (B.atlas.isOriginalChartDomain_chart j))

/-- Every source chart maps into the actual chosen target chart. -/
theorem fromChartPullback_admissible (j : B.atlas.Index)
    (φ : BoundedAlgHom K (B.atlas.algebra j) (P.presentation.atlas.algebra P.topChart))
    (c : P.presentation.atlas.Index) :
    (fromChartPullback P hP j φ).baseMap '' range (P.presentation.atlas.chart c) ⊆
      range (B.atlas.chart j) := by
  rintro _ ⟨x, -, rfl⟩
  exact (TopChartPresentation.ofTopPullback
    (A := P) (B := TopChartPresentation.ofChart B j) φ).baseMap x |>.property

/-- At the whole source chart the complete bounded pullback is exactly the
prescribed map, including coefficient data. -/
theorem fromChartPullback_pullback_top (j : B.atlas.Index)
    (φ : BoundedAlgHom K (B.atlas.algebra j) (P.presentation.atlas.algebra P.topChart))
    (hc : (fromChartPullback P hP j φ).baseMap '' range (P.presentation.atlas.chart P.topChart) ⊆
      range (B.atlas.chart j)) :
    (fromChartPullback P hP j φ).pullback P.topChart j hc = φ := by
  let F := CompatibleStrongHom.ofSaturated
    (TopChartPresentation.ofTopPullback (A := P) (B := TopChartPresentation.ofChart B j) φ) hP
  let I := B.subspaceCompatibleInclusion (range (B.atlas.chart j)) (B.atlas.isOriginalChartDomain_chart j)
  have hF := F.toStrongHom.image_chart_top (B.chartTopIndex j) (B.chartTop_contains j) P.topChart
  have hI : I.baseMap '' range ((B.chartPresentation j).atlas.chart (B.chartTopIndex j)) ⊆
      range (B.atlas.chart j) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have he := CompatibleStrongHom.comp_pullback F I P.topChart (B.chartTopIndex j) j hF hI hc
  change (fromChartPullback P hP j φ).pullback P.topChart j hc = _ at he
  refine he.trans ?_
  have hId : I.pullback (B.chartTopIndex j) j hI = BoundedAlgHom.id K (B.atlas.algebra j) :=
    B.atlas.restriction_id j _
  erw [hId, BoundedAlgHom.comp_id]
  exact (TopChartPresentation.ofTopPullback_pullback_top
    (A := P) (B := TopChartPresentation.ofChart B j) φ P.topChart hF).trans
      (by erw [P.presentation.atlas.restriction_id, BoundedAlgHom.id_comp])

/-- One complete admissible pullback at the whole source chart recovers
any compatible map whose source image lies in the chosen target chart. -/
theorem fromChartPullback_eq (j : B.atlas.Index) (f : CompatibleStrongHom P.presentation B)
    (hf : f.baseMap '' range (P.presentation.atlas.chart P.topChart) ⊆ range (B.atlas.chart j)) :
    fromChartPullback P hP j (f.pullback P.topChart j hf) = f := by
  let g := fromChartPullback P hP j (f.pullback P.topChart j hf)
  have hg := fromChartPullback_admissible P hP j (f.pullback P.topChart j hf) P.topChart
  have he : g.pullback P.topChart j hg = f.pullback P.topChart j hf :=
    fromChartPullback_pullback_top P hP j _ hg
  have hb : g.baseMap = f.baseMap := by
    apply ContinuousMap.ext
    intro x
    obtain ⟨s, rfl⟩ := P.topChart_surjective x
    exact (g.chart_comm P.topChart j hg s).symm.trans
      ((congrArg (fun ψ => B.atlas.chart j (BanachSpectrum.comap ψ.toBoundedRingHom s)) he).trans
        (f.chart_comm P.topChart j hf s))
  refine CompatibleStrongHom.ext_of_pullback hb fun c => ?_
  have hgc := (image_mono (P.top_contains c)).trans hg
  have hfc := (image_mono (P.top_contains c)).trans hf
  exact ⟨j, hgc, (g.toStrongHom.restriction_comp_pullback c P.topChart j
    (P.top_contains c) hgc hg).symm.trans
      ((congrArg (fun ψ => (P.presentation.atlas.restriction c P.topChart (P.top_contains c)).comp ψ)
        he).trans (f.toStrongHom.restriction_comp_pullback c P.topChart j
          (P.top_contains c) hfc hf))⟩

/-- Composition retains the full bounded composite through an admissible
intermediate chart in the original compatible category. -/
theorem fromChartPullback_comp (j : B.atlas.Index)
    (φ : BoundedAlgHom K (B.atlas.algebra j) (P.presentation.atlas.algebra P.topChart))
    (g : CompatibleStrongHom B C) (k : C.atlas.Index)
    (hg : g.baseMap '' range (B.atlas.chart j) ⊆ range (C.atlas.chart k)) :
    (fromChartPullback P hP j φ).comp g = fromChartPullback P hP k (φ.comp (g.pullback j k hg)) := by
  let f := fromChartPullback P hP j φ
  have hf := fromChartPullback_admissible P hP j φ P.topChart
  have hfg : (f.comp g).baseMap '' range (P.presentation.atlas.chart P.topChart) ⊆
      range (C.atlas.chart k) := f.toStrongHom.comp_admissible g.toStrongHom _ j k hf hg
  have he : (f.comp g).pullback P.topChart k hfg = φ.comp (g.pullback j k hg) :=
    (CompatibleStrongHom.comp_pullback f g P.topChart j k hf hg hfg).trans
      (congrArg (fun ψ => ψ.comp (g.pullback j k hg))
        (fromChartPullback_pullback_top P hP j φ hf))
  exact (fromChartPullback_eq P hP k (f.comp g) hfg).symm.trans
    (congrArg (fromChartPullback P hP k) he)

end Langlands.Analytic.AffinoidAtlasPresentation.CompatibleStrongHom
