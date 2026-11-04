import Langlands.Geometry.Analytic.AtlasDomainRepresentation

/-! # Target-chart change for arbitrary bounded affinoid maps -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Agreement over one original chart forces agreement over another for
arbitrary affinoid tests into two common subcharts. The tests need not themselves
represent domains in either containing chart. -/
theorem originalChartRestriction_test_overlap (i j k l : a.Index)
    (hki : Set.range (a.chart k) ⊆ Set.range (a.chart i))
    (hkj : Set.range (a.chart k) ⊆ Set.range (a.chart j))
    (hli : Set.range (a.chart l) ⊆ Set.range (a.chart i))
    (hlj : Set.range (a.chart l) ⊆ Set.range (a.chart j))
    (R : PresentedAffinoidAlgebra K)
    (α : BoundedAlgHom K (a.algebra k) R)
    (β : BoundedAlgHom K (a.algebra l) R)
    (h : α.comp (a.restriction k i hki) = β.comp (a.restriction l i hli)) :
    α.comp (a.restriction k j hkj) = β.comp (a.restriction l j hlj) := by
  let D := a.restrictionDomain k i hki
  let E := a.restrictionDomain l i hli
  let W := D.inter E
  have himage : HasImageIn K (α.comp D.baseMap) W.locus := by
    intro x
    refine ⟨D.represents.hasImageIn (BanachSpectrum.comap α.toBoundedRingHom x), ?_⟩
    have hx := E.represents.hasImageIn (BanachSpectrum.comap β.toBoundedRingHom x)
    have heq : BanachSpectrum.comap (α.comp D.baseMap).toBoundedRingHom x =
        BanachSpectrum.comap (β.comp E.baseMap).toBoundedRingHom x :=
      congrArg (fun q : BoundedAlgHom K (a.algebra i) R =>
        BanachSpectrum.comap q.toBoundedRingHom x) h
    exact heq.symm ▸ hx
  obtain ⟨θ, hθ, _⟩ := W.represents.2.2 R (α.comp D.baseMap) himage
  have hα : θ.comp (Domain.interLeft D E).restriction = α := by
    apply D.represents.hom_ext R
    erw [BoundedAlgHom.comp_assoc, (Domain.interLeft D E).comp_baseMap, hθ]
    rfl
  have hβ : θ.comp (Domain.interRight D E).restriction = β := by
    apply E.represents.hom_ext R
    erw [BoundedAlgHom.comp_assoc, (Domain.interRight D E).comp_baseMap, hθ]
    exact h
  have hover := a.originalChartRestriction_overlap i j k l hki hkj hli hlj W
    (Domain.interLeft D E) (Domain.interRight D E)
  calc
    α.comp (a.restriction k j hkj) =
        (θ.comp (Domain.interLeft D E).restriction).comp (a.restriction k j hkj) :=
      congrArg (fun q : BoundedAlgHom K (a.algebra k) R =>
        q.comp (a.restriction k j hkj)) hα.symm
    _ = (θ.comp (Domain.interRight D E).restriction).comp (a.restriction l j hlj) :=
      congrArg (fun q : BoundedAlgHom K (a.algebra j) W.algebra => θ.comp q) hover
    _ = β.comp (a.restriction l j hlj) :=
      congrArg (fun q : BoundedAlgHom K (a.algebra l) R =>
        q.comp (a.restriction l j hlj)) hβ

namespace CompactIntersectionChartCover

variable {a} {i j : a.Index} {S : Set X}
  (c : a.CompactIntersectionChartCover i j S)
  (R : PresentedAffinoidAlgebra K) (φ : BoundedAlgHom K (a.algebra i) R)
  (hφ : ∀ x : BanachSpectrum R,
    a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ S)

/-- The actual inverse-image quotients of the original relative chart domains
cover the whole arbitrary test spectrum. -/
def mapPullbackCover : Domain.FiniteCover (Domain.whole K R) where
  size := c.size
  obj t := Domain.pullback φ (a.restrictionDomain (c.index t) i (c.left_subset t))
  map t := ⟨(Domain.pullback φ
    (a.restrictionDomain (c.index t) i (c.left_subset t))).baseMap,
    BoundedAlgHom.comp_id _⟩
  covers x _ := c.covers _ (hφ x)

/-- The second actual quotient projection followed by the original target
restriction gives the local coefficient map. -/
def mapPullbackFamily (t : Fin c.size) :
    BoundedAlgHom K (a.algebra j) ((c.mapPullbackCover R φ hφ).obj t).algebra :=
  (Domain.pullbackMap φ (a.restrictionDomain (c.index t) i (c.left_subset t))).comp
    (a.restriction (c.index t) j (c.right_subset t))

theorem mapPullbackFamily_compatible :
    (c.mapPullbackCover R φ hφ).BoundedMapCompatible (c.mapPullbackFamily R φ hφ) := by
  intro t s W p q
  let α := p.restriction.comp
    (Domain.pullbackMap φ (a.restrictionDomain (c.index t) i (c.left_subset t)))
  let β := q.restriction.comp
    (Domain.pullbackMap φ (a.restrictionDomain (c.index s) i (c.left_subset s)))
  have hα : α.comp (a.restriction (c.index t) i (c.left_subset t)) =
      W.baseMap.comp φ := by
    erw [BoundedAlgHom.comp_assoc, Domain.pullbackMap_comp_baseMap,
      ← BoundedAlgHom.comp_assoc, p.comp_baseMap]
  have hβ : β.comp (a.restriction (c.index s) i (c.left_subset s)) =
      W.baseMap.comp φ := by
    erw [BoundedAlgHom.comp_assoc, Domain.pullbackMap_comp_baseMap,
      ← BoundedAlgHom.comp_assoc, q.comp_baseMap]
  exact a.originalChartRestriction_test_overlap i j (c.index t) (c.index s)
    (c.left_subset t) (c.right_subset t) (c.left_subset s) (c.right_subset s)
    W.algebra α β (hα.trans hβ.symm)

/-- Bounded descent constructs the new coefficient map into the unchanged
arbitrary test algebra. -/
def glueMapChartChange : BoundedAlgHom K (a.algebra j) R :=
  (c.mapPullbackCover R φ hφ).glueBoundedAlgHom (c.mapPullbackFamily R φ hφ)
    (c.mapPullbackFamily_compatible R φ hφ)

theorem glueMapChartChange_local (t : Fin c.size) :
    (Domain.pullback φ
        (a.restrictionDomain (c.index t) i (c.left_subset t))).baseMap.comp
        (c.glueMapChartChange R φ hφ) =
      c.mapPullbackFamily R φ hφ t :=
  (c.mapPullbackCover R φ hφ).restriction_comp_glueBoundedAlgHom _ _ t

/-- Each pulled-back bounded map retains the original ambient chart equation. -/
theorem mapPullbackFamily_chart (t : Fin c.size)
    (y : BanachSpectrum ((c.mapPullbackCover R φ hφ).obj t).algebra) :
    a.chart j (BanachSpectrum.comap
        (c.mapPullbackFamily R φ hφ t).toBoundedRingHom y) =
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom
        (((c.mapPullbackCover R φ hφ).obj t).spectrumMap y)) := by
  let D := a.restrictionDomain (c.index t) i (c.left_subset t)
  calc
    a.chart j (BanachSpectrum.comap
        (c.mapPullbackFamily R φ hφ t).toBoundedRingHom y) =
        a.chart (c.index t) (Domain.pullbackSpectrumMap φ D y) :=
      a.restriction_chart (c.index t) j (c.right_subset t)
        (Domain.pullbackSpectrumMap φ D y)
    _ = a.chart i (D.spectrumMap (Domain.pullbackSpectrumMap φ D y)) :=
      (a.restriction_chart (c.index t) i (c.left_subset t) _).symm
    _ = a.chart i (BanachSpectrum.comap φ.toBoundedRingHom
        (((c.mapPullbackCover R φ hφ).obj t).spectrumMap y)) :=
      congrArg (a.chart i) (Domain.pullbackSpectrumMap_over_base φ D y)

/-- Coverage of the actual source spectrum and the exact bounded descent
equations recover the chart equation at every source point. -/
theorem glueMapChartChange_chart (x : BanachSpectrum R) :
    a.chart j (BanachSpectrum.comap (c.glueMapChartChange R φ hφ).toBoundedRingHom x) =
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) := by
  obtain ⟨t, ht⟩ := (c.mapPullbackCover R φ hφ).covers x (Set.mem_univ _)
  obtain ⟨y, hy⟩ := ((c.mapPullbackCover R φ hφ).obj t).represents.2.1.symm ▸ ht
  have heq :
      BanachSpectrum.comap (c.glueMapChartChange R φ hφ).toBoundedRingHom
          (((c.mapPullbackCover R φ hφ).obj t).spectrumMap y) =
        BanachSpectrum.comap (c.mapPullbackFamily R φ hφ t).toBoundedRingHom y := by
    apply BanachSpectrum.ext
    intro b
    exact congrArg (fun q : BoundedAlgHom K (a.algebra j)
      ((c.mapPullbackCover R φ hφ).obj t).algebra => y (q b))
      (c.glueMapChartChange_local R φ hφ t)
  change ((c.mapPullbackCover R φ hφ).obj t).spectrumMap y = x at hy
  rw [← hy, heq]
  exact c.mapPullbackFamily_chart R φ hφ t y

end CompactIntersectionChartCover

/-- The actual compact image of an arbitrary affinoid test map. -/
def mapChartImage (i : a.Index) (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra i) R) : Set X :=
  Set.range (fun x => a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x))

/-- The original net supplies a finite common-chart cover of that image. -/
def mapImageChartCover (i j : a.Index) (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra i) R)
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j)) :
    a.CompactIntersectionChartCover i j (a.mapChartImage i R φ) :=
  a.compactIntersectionChartCover i j (a.mapChartImage i R φ)
    (isCompact_range ((a.isEmbedding_chart i).continuous.comp
      (BanachSpectrum.comapContinuous φ.toBoundedRingHom).continuous))
    (by rintro _ ⟨x, rfl⟩; exact ⟨⟨_, rfl⟩, h x⟩)

/-- Construct the bounded coefficient map in any original target chart
containing the entire image of an arbitrary affinoid test. -/
def changeMapChart (i j : a.Index) (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra i) R)
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j)) :
    BoundedAlgHom K (a.algebra j) R :=
  (a.mapImageChartCover i j R φ h).glueMapChartChange R φ (fun x => ⟨x, rfl⟩)

theorem changeMapChart_chart (i j : a.Index) (R : PresentedAffinoidAlgebra K)
    (φ : BoundedAlgHom K (a.algebra i) R)
    (h : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ Set.range (a.chart j))
    (x : BanachSpectrum R) :
    a.chart j (BanachSpectrum.comap (a.changeMapChart i j R φ h).toBoundedRingHom x) =
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) :=
  (a.mapImageChartCover i j R φ h).glueMapChartChange_chart R φ
    (fun x => ⟨x, rfl⟩) x

end Langlands.Analytic.IndexedAffinoidAtlas
