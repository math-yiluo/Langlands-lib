import Langlands.Geometry.Analytic.CoherentStrongChartChange
import Langlands.Geometry.Analytic.AtlasDomainMapChartChange
import Langlands.Geometry.Analytic.SaturatedStrongComposition

/-! # Constructed strong pullbacks on arbitrary source local domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Every local source domain maps into a target chart chosen for its parent. -/
theorem localDomain_chosenTarget_admissible (f : StrongHom A B)
    (U : LocalDomain A.atlas) :
    f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart (f.chosenTargetIndex U.index)) := by
  rintro _ ⟨x, ⟨y, _, hy⟩, rfl⟩
  exact f.chosenTarget_admissible U.index ⟨x, ⟨y, hy⟩, rfl⟩

/-- The parent-chart bounded map has its entire spectrum image in every
original target chart containing the local-domain image. -/
theorem localDomain_parentPullback_image (f : StrongHom A B)
    (U : LocalDomain A.atlas) (j : B.atlas.Index)
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j))
    (x : BanachSpectrum U.algebra) :
    B.atlas.chart (f.chosenTargetIndex U.index)
      (BanachSpectrum.comap
        (f.mapAffinoidChart U.index (f.chosenTargetIndex U.index)
          (f.chosenTarget_admissible U.index) U.algebra U.domain.baseMap).toBoundedRingHom x)
      ∈ Set.range (B.atlas.chart j) := by
  rw [f.mapAffinoidChart_chart]
  exact h ⟨U.ambientMap x,
    ⟨U.domain.spectrumMap x, U.domain.represents.hasImageIn x, rfl⟩, rfl⟩

/-- Restrict the original parent pullback to the actual domain algebra and
change to any original target chart containing this domain's image. -/
def localChartPullback (f : StrongHom A B) (U : LocalDomain A.atlas)
    (j : B.atlas.Index)
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j)) :
    BoundedAlgHom K (B.atlas.algebra j) U.algebra :=
  B.atlas.changeMapChart (f.chosenTargetIndex U.index) j U.algebra
    (f.mapAffinoidChart U.index (f.chosenTargetIndex U.index)
      (f.chosenTarget_admissible U.index) U.algebra U.domain.baseMap)
    (f.localDomain_parentPullback_image U j h)

theorem localChartPullback_chart (f : StrongHom A B) (U : LocalDomain A.atlas)
    (j : B.atlas.Index)
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j))
    (x : BanachSpectrum U.algebra) :
    B.atlas.chart j (BanachSpectrum.comap (f.localChartPullback U j h).toBoundedRingHom x) =
      f.baseMap (U.ambientMap x) := by
  unfold localChartPullback
  rw [B.atlas.changeMapChart_chart, f.mapAffinoidChart_chart]
  rfl

/-- Every second target change gives the direct constructed domain pullback. -/
theorem localChartPullback_change (f : StrongHom A B) (U : LocalDomain A.atlas)
    (j k : B.atlas.Index)
    (hj : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j))
    (hk : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart k))
    (hjk : ∀ x : BanachSpectrum U.algebra,
      B.atlas.chart j (BanachSpectrum.comap (f.localChartPullback U j hj).toBoundedRingHom x)
        ∈ Set.range (B.atlas.chart k)) :
    B.atlas.changeMapChart j k U.algebra (f.localChartPullback U j hj) hjk =
      f.localChartPullback U k hk :=
  B.atlas.changeMapChart_trans _ j k U.algebra _
    (f.localDomain_parentPullback_image U j hj)
    (f.localDomain_parentPullback_image U k hk) hjk

/-- The constructed local family satisfies the full target coefficient-test
law, independently of the chosen original parent target. -/
theorem localChartPullback_isMapChartChange (f : StrongHom A B)
    (U : LocalDomain A.atlas) (j k : B.atlas.Index)
    (hj : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j))
    (hk : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart k)) :
    B.atlas.IsMapChartChange j k U.algebra
      (f.localChartPullback U j hj) (f.localChartPullback U k hk) := by
  have hchange (x : BanachSpectrum U.algebra) :
      B.atlas.chart j (BanachSpectrum.comap (f.localChartPullback U j hj).toBoundedRingHom x)
        ∈ Set.range (B.atlas.chart k) := by
    rw [f.localChartPullback_chart]
    exact hk ⟨U.ambientMap x,
      ⟨U.domain.spectrumMap x, U.domain.represents.hasImageIn x, rfl⟩, rfl⟩
  rw [← f.localChartPullback_change U j k hj hk hchange]
  exact B.atlas.changeMapChart_isMapChartChange j k U.algebra _ hchange

/-- Intrinsic coherence recovers the original map for any target containing
the whole parent chart, after restriction to the unchanged domain algebra. -/
theorem localChartPullback_of_parent_admissible (f : StrongHom A B)
    (hf : f.HasCoherentPullbacks) (U : LocalDomain A.atlas) (j : B.atlas.Index)
    (hj : f.baseMap '' Set.range (A.atlas.chart U.index) ⊆ Set.range (B.atlas.chart j))
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j)) :
    f.localChartPullback U j h = U.domain.baseMap.comp (f.pullback U.index j hj) :=
  (B.atlas.eq_changeMapChart _ j U.algebra _
    (f.localDomain_parentPullback_image U j h) _
    ((hf U.index _ j (f.chosenTarget_admissible U.index) hj).comp B.atlas
      U.domain.baseMap)).symm

/-- Under the original-map coherence law, every actual local-domain inclusion
commutes with the constructed pullbacks to a fixed original target chart. -/
theorem localChartPullback_source (f : StrongHom A B) (hf : f.HasCoherentPullbacks)
    {U V : LocalDomain A.atlas} (p : U ⟶ V) (j : B.atlas.Index)
    (hU : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j))
    (hV : f.baseMap '' V.locus ⊆ Set.range (B.atlas.chart j)) :
    p.restriction.comp (f.localChartPullback V j hV) = f.localChartPullback U j hU := by
  let k := f.chosenTargetIndex U.index
  let l := f.chosenTargetIndex V.index
  let φ := f.mapAffinoidChart U.index k (f.chosenTarget_admissible U.index)
    U.algebra U.domain.baseMap
  let ψ := f.mapAffinoidChart V.index l (f.chosenTarget_admissible V.index)
    V.algebra V.domain.baseMap
  have hsource :
      A.atlas.IsMapChartChange U.index V.index U.algebra U.domain.baseMap
        (p.restriction.comp V.domain.baseMap) := by
    rw [p.restriction_eq]
    exact A.atlas.domainRestriction_isMapChartChange U.index V.index U.domain V.domain p.subset
  have hparent := f.mapAffinoidChart_isMapChartChange_of_coherent hf U.index V.index k l
    (f.chosenTarget_admissible U.index) (f.chosenTarget_admissible V.index)
    U.algebra U.domain.baseMap (p.restriction.comp V.domain.baseMap)
    (A.atlas.domainBaseMap_image_chart U.index V.index U.domain
      (A.atlas.domainSubset_chart U.index V.index U.domain V.domain p.subset)) hsource
  have himage : ∀ x : BanachSpectrum U.algebra,
      B.atlas.chart k (BanachSpectrum.comap φ.toBoundedRingHom x) ∈
        Set.range (B.atlas.chart l) :=
    f.localDomain_parentPullback_image U l
      ((Set.image_mono p.subset).trans (f.localDomain_chosenTarget_admissible V))
  have htarget :
      B.atlas.IsMapChartChange l j U.algebra (p.restriction.comp ψ)
        (p.restriction.comp (f.localChartPullback V j hV)) :=
    (B.atlas.changeMapChart_isMapChartChange l j V.algebra ψ
      (f.localDomain_parentPullback_image V j hV)).comp B.atlas p.restriction
  exact B.atlas.eq_changeMapChart k j U.algebra φ
    (f.localDomain_parentPullback_image U j hU) _
    (hparent.trans B.atlas himage htarget)

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
