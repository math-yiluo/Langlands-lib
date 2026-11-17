import Langlands.Geometry.Analytic.TopChartAffinoidComparison
import Langlands.Geometry.Analytic.SaturatedDomainCorestriction

/-! # Maps from a global chart into arbitrary saturated presentations -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set CategoryTheory IndexedAffinoidAtlas AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace SaturatedAtlasPresentation

variable {A B C : SaturatedAtlasPresentation.{u, v, w} K}

/-- Regard the global chart of a saturated presentation as its greatest chart. -/
def globalChartPresentation (A : SaturatedAtlasPresentation.{u, v, w} K)
    (i : A.presentation.atlas.Index)
    (hi : range (A.presentation.atlas.chart i) = univ) :
    TopChartPresentation.{u, v, w} K where
  presentation := A.presentation
  topChart := i
  top_contains _ := hi.symm ▸ subset_univ _

/-- Construct a full strong map from its bounded pullback into one target
chart, by first mapping to that chart's actual domain and then including it. -/
def chartSourceMap
    (i : A.presentation.atlas.Index)
    (hi : range (A.presentation.atlas.chart i) = univ)
    (j : B.presentation.atlas.Index)
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra j)
      (A.presentation.atlas.algebra i)) : A ⟶ B :=
  (TopChartPresentation.ofTopPullback
    (A := A.globalChartPresentation i hi)
    (B := TopChartPresentation.ofChart B.presentation j) φ).saturatedComp
      (B.originalDomainInclusion (OriginalChartDomain.ofChart j))
      A.hasAllLocalDomains
      (B.originalDomain (OriginalChartDomain.ofChart j)).hasAllLocalDomains

/-- The source map has image in its selected actual target chart. -/
theorem chartSourceMap_admissible
    (i : A.presentation.atlas.Index)
    (hi : range (A.presentation.atlas.chart i) = univ)
    (j : B.presentation.atlas.Index)
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra j)
      (A.presentation.atlas.algebra i)) (c : A.presentation.atlas.Index) :
    (chartSourceMap i hi j φ).baseMap '' range (A.presentation.atlas.chart c) ⊆
      range (B.presentation.atlas.chart j) := by
  rintro _ ⟨x, _, rfl⟩
  exact (TopChartPresentation.ofTopPullback
    (A := A.globalChartPresentation i hi)
    (B := TopChartPresentation.ofChart B.presentation j) φ).baseMap x |>.property

/-- At every source chart the selected-target pullback is the original
source restriction followed by the prescribed bounded map. -/
theorem chartSourceMap_pullback
    (i : A.presentation.atlas.Index)
    (hi : range (A.presentation.atlas.chart i) = univ)
    (j : B.presentation.atlas.Index)
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra j)
      (A.presentation.atlas.algebra i)) (c : A.presentation.atlas.Index)
    (hc : (chartSourceMap i hi j φ).baseMap '' range (A.presentation.atlas.chart c) ⊆
      range (B.presentation.atlas.chart j)) :
    (chartSourceMap i hi j φ).pullback c j hc =
      (A.presentation.atlas.restriction c i (hi.symm ▸ subset_univ _)).comp φ := by
  let F : StrongHom A.presentation (B.presentation.chartPresentation j) :=
    TopChartPresentation.ofTopPullback
    (A := A.globalChartPresentation i hi)
    (B := TopChartPresentation.ofChart B.presentation j) φ
  have hF := F.image_chart_top (B.presentation.chartTopIndex j)
    (B.presentation.chartTop_contains j) c
  have hJ : (B.originalDomainInclusion (OriginalChartDomain.ofChart j)).baseMap ''
      range ((B.originalDomain (OriginalChartDomain.ofChart j)).presentation.atlas.chart
        (B.presentation.chartTopIndex j)) ⊆ range (B.presentation.atlas.chart j) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hI : (B.originalDomainInclusion (OriginalChartDomain.ofChart j)).pullback
      (B.presentation.chartTopIndex j) j hJ =
      BoundedAlgHom.id K (B.presentation.atlas.algebra j) :=
    B.presentation.atlas.restriction_id j _
  exact (StrongHom.saturatedComp_pullback F
    (B.originalDomainInclusion (OriginalChartDomain.ofChart j))
    A.hasAllLocalDomains
    (B.originalDomain (OriginalChartDomain.ofChart j)).hasAllLocalDomains
    c (B.presentation.chartTopIndex j) j hF hJ hc).trans
      ((congrArg (fun ψ => (F.pullback c (B.presentation.chartTopIndex j) hF).comp ψ)
        hI).trans ((BoundedAlgHom.comp_id _).trans
          (TopChartPresentation.ofTopPullback_pullback_top
            (A := A.globalChartPresentation i hi)
            (B := TopChartPresentation.ofChart B.presentation j) φ c hF)))

/-- The global pullback is exactly the supplied bounded map. -/
theorem chartSourceMap_pullback_global
    (i : A.presentation.atlas.Index)
    (hi : range (A.presentation.atlas.chart i) = univ)
    (j : B.presentation.atlas.Index)
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra j)
      (A.presentation.atlas.algebra i))
    (h : (chartSourceMap i hi j φ).baseMap '' range (A.presentation.atlas.chart i) ⊆
      range (B.presentation.atlas.chart j)) :
    (chartSourceMap i hi j φ).pullback i j h = φ := by
  rw [chartSourceMap_pullback, A.presentation.atlas.restriction_id,
    BoundedAlgHom.id_comp]

/-- The actual point map is the spectrum map prescribed on the global chart. -/
theorem chartSourceMap_chart
    (i : A.presentation.atlas.Index)
    (hi : range (A.presentation.atlas.chart i) = univ)
    (j : B.presentation.atlas.Index)
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra j)
      (A.presentation.atlas.algebra i))
    (s : BanachSpectrum (A.presentation.atlas.algebra i)) :
    (chartSourceMap i hi j φ).baseMap (A.presentation.atlas.chart i s) =
      B.presentation.atlas.chart j (BanachSpectrum.comap φ.toBoundedRingHom s) := by
  have h := (chartSourceMap i hi j φ).chart_comm i j
    (chartSourceMap_admissible i hi j φ i) s
  rw [chartSourceMap_pullback_global] at h
  exact h.symm

/-- Any full strong map into the chosen chart is recovered from its complete
global bounded pullback. -/
theorem chartSourceMap_eq
    (i : A.presentation.atlas.Index)
    (hi : range (A.presentation.atlas.chart i) = univ)
    (j : B.presentation.atlas.Index) (f : A ⟶ B)
    (hf : f.baseMap '' range (A.presentation.atlas.chart i) ⊆
      range (B.presentation.atlas.chart j)) :
    chartSourceMap i hi j (f.pullback i j hf) = f := by
  let g := chartSourceMap i hi j (f.pullback i j hf)
  have hg := chartSourceMap_admissible i hi j (f.pullback i j hf) i
  have he : g.pullback i j hg = f.pullback i j hf :=
    chartSourceMap_pullback_global i hi j (f.pullback i j hf) hg
  have hb : g.baseMap = f.baseMap := by
    apply ContinuousMap.ext
    intro x
    obtain ⟨s, rfl⟩ := hi.symm ▸ mem_univ x
    exact (g.chart_comm i j hg s).symm.trans
      ((congrArg (fun ψ => B.presentation.atlas.chart j
        (BanachSpectrum.comap ψ.toBoundedRingHom s)) he).trans
          (f.chart_comm i j hf s))
  refine StrongHom.ext_of_saturated A.hasAllLocalDomains hb ?_
  intro c
  have hci : range (A.presentation.atlas.chart c) ⊆
      range (A.presentation.atlas.chart i) := hi.symm ▸ subset_univ _
  have hgc := (Set.image_mono hci).trans hg
  have hfc := (Set.image_mono hci).trans hf
  exact ⟨j, hgc,
    (g.restriction_comp_pullback c i j hci hgc hg).symm.trans
      ((congrArg (fun ψ => (A.presentation.atlas.restriction c i hci).comp ψ) he).trans
        (f.restriction_comp_pullback c i j hci hfc hf))⟩

/-- Composition retains the complete bounded composite whenever the chosen
intermediate chart is admissible for the second map. -/
theorem chartSourceMap_comp
    (i : A.presentation.atlas.Index)
    (hi : range (A.presentation.atlas.chart i) = univ)
    (j : B.presentation.atlas.Index)
    (φ : BoundedAlgHom K (B.presentation.atlas.algebra j)
      (A.presentation.atlas.algebra i)) (g : B ⟶ C)
    (k : C.presentation.atlas.Index)
    (hg : g.baseMap '' range (B.presentation.atlas.chart j) ⊆
      range (C.presentation.atlas.chart k)) :
    chartSourceMap i hi j φ ≫ g =
      chartSourceMap i hi k (φ.comp (g.pullback j k hg)) := by
  let f := chartSourceMap i hi j φ
  have hf := chartSourceMap_admissible i hi j φ i
  have hfg : (f ≫ g).baseMap '' range (A.presentation.atlas.chart i) ⊆
      range (C.presentation.atlas.chart k) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg ⟨f.baseMap x, hf ⟨x, hx, rfl⟩, rfl⟩
  have he : (f ≫ g).pullback i k hfg = φ.comp (g.pullback j k hg) :=
    (f.saturatedComp_pullback g A.hasAllLocalDomains B.hasAllLocalDomains
      i j k hf hg hfg).trans
        (congrArg (fun ψ => ψ.comp (g.pullback j k hg))
          (chartSourceMap_pullback_global i hi j φ hf))
  exact (chartSourceMap_eq i hi k (f ≫ g) hfg).symm.trans
    (congrArg (chartSourceMap i hi k) he)

end SaturatedAtlasPresentation

end Langlands.Analytic
