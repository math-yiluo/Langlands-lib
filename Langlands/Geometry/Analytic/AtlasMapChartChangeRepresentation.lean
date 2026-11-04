import Langlands.Geometry.Analytic.AtlasMapChartChangeCoherence

/-! # Full affinoid-domain representations under arbitrary chart change -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Reversal satisfies the full coefficient-test law, with the original
bounded map as its result. -/
theorem changeMapChart_reverse_isMapChartChange (i j : a.Index)
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (a.algebra i) R)
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j)) :
    a.IsMapChartChange j i R (a.changeMapChart i j R φ h) φ := by
  have hr := a.changeMapChart_isMapChartChange j i R
    (a.changeMapChart i j R φ h) (a.changeMapChart_image_original i j R φ h)
  change a.IsMapChartChange j i R (a.changeMapChart i j R φ h)
    (a.reverseMapChartChange i j R φ h) at hr
  rw [a.reverseMapChartChange_eq] at hr
  exact hr

/-- A full domain representation in one original chart remains a full
representation in every chart containing its entire ambient image. -/
theorem represents_changeMapChart (i j : a.Index)
    (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (a.algebra i) R)
    {U : Set (BanachSpectrum (a.algebra i))} (hrep : Represents K φ U)
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j)) :
    Represents K (a.changeMapChart i j R φ h)
      (a.chart j ⁻¹' a.mapChartImage i R φ) := by
  let φj := a.changeMapChart i j R φ h
  have hrange : Set.range (BanachSpectrum.comap φj.toBoundedRingHom) =
      a.chart j ⁻¹' a.mapChartImage i R φ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, (a.changeMapChart_chart i j R φ h x).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, (a.isEmbedding_chart j).injective ?_⟩
      exact (a.changeMapChart_chart i j R φ h x).trans hx
  refine ⟨?_, hrange, ?_⟩
  · rw [← hrange]
    exact (isCompact_range
      (BanachSpectrum.comapContinuous φj.toBoundedRingHom).continuous).isClosed
  · intro T ψ hψ
    have hψi : ∀ x : BanachSpectrum T,
        a.chart j (BanachSpectrum.comap ψ.toBoundedRingHom x) ∈
          Set.range (a.chart i) := by
      intro x
      obtain ⟨y, hy⟩ := hψ x
      exact ⟨_, hy⟩
    let χ := a.changeMapChart j i T ψ hψi
    have hχ : HasImageIn K χ U := by
      intro x
      obtain ⟨y, hy⟩ := hψ x
      have heq : BanachSpectrum.comap χ.toBoundedRingHom x =
          BanachSpectrum.comap φ.toBoundedRingHom y := by
        apply (a.isEmbedding_chart i).injective
        exact (a.changeMapChart_chart j i T ψ hψi x).trans hy.symm
      rw [heq]
      exact hrep.hasImageIn y
    obtain ⟨η, hη, huniq⟩ := hrep.2.2 T χ hχ
    have hχj := a.changeMapChart_image_original j i T ψ hψi
    refine ⟨η, ?_, ?_⟩
    · have hforward : a.IsMapChartChange i j T χ (η.comp φj) := by
        rw [← hη]
        exact (a.changeMapChart_isMapChartChange i j R φ h).comp a η
      exact (a.eq_changeMapChart i j T χ hχj _ hforward).trans
        (a.reverseMapChartChange_eq j i T ψ hψi)
    · intro θ hθ
      apply huniq θ
      have hreverse := (a.changeMapChart_reverse_isMapChartChange i j R φ h).comp a θ
      change a.IsMapChartChange j i T (θ.comp φj) (θ.comp φ) at hreverse
      rw [hθ] at hreverse
      exact a.eq_changeMapChart j i T ψ hψi _ hreverse

/-- Move an actual full domain to another original chart while retaining
its literal presented algebra and using the constructed bounded chart change. -/
def changeDomainChart (i j : a.Index) (D : Domain K (a.algebra i))
    (h : a.chart i '' D.locus ⊆ Set.range (a.chart j)) :
    Domain K (a.algebra j) where
  algebra := D.algebra
  baseMap := a.changeMapChart i j D.algebra D.baseMap
    (fun x => h ⟨_, D.represents.hasImageIn x, rfl⟩)
  locus := a.chart j ⁻¹' (a.chart i '' D.locus)
  represents := by
    have himage : a.mapChartImage i D.algebra D.baseMap = a.chart i '' D.locus := by
      rw [mapChartImage, ← D.represents.2.1]
      exact Set.range_comp _ _
    rw [← himage]
    exact a.represents_changeMapChart i j D.algebra D.baseMap D.represents _

@[simp]
theorem changeDomainChart_algebra (i j : a.Index) (D : Domain K (a.algebra i))
    (h : a.chart i '' D.locus ⊆ Set.range (a.chart j)) :
    (a.changeDomainChart i j D h).algebra = D.algebra := rfl

@[simp]
theorem changeDomainChart_baseMap (i j : a.Index) (D : Domain K (a.algebra i))
    (h : a.chart i '' D.locus ⊆ Set.range (a.chart j)) :
    (a.changeDomainChart i j D h).baseMap =
      a.changeMapChart i j D.algebra D.baseMap
        (fun x => h ⟨_, D.represents.hasImageIn x, rfl⟩) := rfl

@[simp]
theorem changeDomainChart_locus (i j : a.Index) (D : Domain K (a.algebra i))
    (h : a.chart i '' D.locus ⊆ Set.range (a.chart j)) :
    (a.changeDomainChart i j D h).locus = a.chart j ⁻¹' (a.chart i '' D.locus) := rfl

end Langlands.Analytic.IndexedAffinoidAtlas
