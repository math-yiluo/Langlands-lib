import Langlands.Geometry.Analytic.AtlasDomainChartCover
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBoundedMapGluing

/-! # Bounded original-chart restrictions into arbitrary contained local domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Original restrictions to two charts inside the same two ambient charts
agree on every actual full domain mapping to both. -/
theorem originalChartRestriction_overlap (i j k l : a.Index)
    (hki : Set.range (a.chart k) ⊆ Set.range (a.chart i))
    (hkj : Set.range (a.chart k) ⊆ Set.range (a.chart j))
    (hli : Set.range (a.chart l) ⊆ Set.range (a.chart i))
    (hlj : Set.range (a.chart l) ⊆ Set.range (a.chart j))
    (W : Domain K (a.algebra i))
    (f : W ⟶ a.restrictionDomain k i hki)
    (g : W ⟶ a.restrictionDomain l i hli) :
    f.restriction.comp (a.restriction k j hkj) =
      g.restriction.comp (a.restriction l j hlj) := by
  let d := a.compactIntersectionChartCover k l (a.chart i '' W.locus)
    (W.isCompact_locus.image (a.isEmbedding_chart i).continuous)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨f.subset hx, g.subset hx⟩)
  let c : a.CompactIntersectionChartCover i j (a.chart i '' W.locus) :=
    ⟨d.size, d.index, fun t => (d.left_subset t).trans hki,
      fun t => (d.left_subset t).trans hkj, d.covers⟩
  have hlocal (t : Fin c.size) :
      (c.domainCover.map t).restriction.comp f.restriction =
        (c.domainCoverToChart t).restriction.comp
          (a.restriction (c.index t) k (d.left_subset t)) := by
    apply a.restriction_hom_ext k i hki (c.domainCover.obj t).algebra
    erw [BoundedAlgHom.comp_assoc, f.comp_baseMap,
      BoundedAlgHom.comp_assoc,
      ← a.restriction_comp (c.index t) k i (d.left_subset t) hki (c.left_subset t)]
    exact (c.domainCover.map t).comp_baseMap.trans
      (c.domainCoverToChart t).comp_baseMap.symm
  have hlocal' (t : Fin c.size) :
      (c.domainCover.map t).restriction.comp g.restriction =
        (c.domainCoverToChart t).restriction.comp
          (a.restriction (c.index t) l (d.right_subset t)) := by
    apply a.restriction_hom_ext l i hli (c.domainCover.obj t).algebra
    erw [BoundedAlgHom.comp_assoc, g.comp_baseMap,
      BoundedAlgHom.comp_assoc,
      ← a.restriction_comp (c.index t) l i (d.right_subset t) hli (c.left_subset t)]
    exact (c.domainCover.map t).comp_baseMap.trans
      (c.domainCoverToChart t).comp_baseMap.symm
  apply BoundedAlgHom.ext
  intro b
  apply c.domainCover.algebra_ext_of_restrict_eq
  intro t
  have heq :
      (c.domainCover.map t).restriction.comp
          (f.restriction.comp (a.restriction k j hkj)) =
        (c.domainCover.map t).restriction.comp
          (g.restriction.comp (a.restriction l j hlj)) := by
    erw [← BoundedAlgHom.comp_assoc, hlocal,
      BoundedAlgHom.comp_assoc,
      ← a.restriction_comp (c.index t) k j (d.left_subset t) hkj (c.right_subset t),
      ← BoundedAlgHom.comp_assoc, hlocal',
      BoundedAlgHom.comp_assoc,
      ← a.restriction_comp (c.index t) l j (d.right_subset t) hlj (c.right_subset t)]
  exact congrArg (fun q : BoundedAlgHom K (a.algebra j)
    (c.domainCover.obj t).algebra => q b) heq

namespace CompactIntersectionChartCover

variable {a} {i j : a.Index} {U : Domain K (a.algebra i)}
  (c : a.CompactIntersectionChartCover i j (a.chart i '' U.locus))

/-- The actual structural maps of the transported covering domains. -/
def chartRestrictionFamily (t : Fin c.size) :
    BoundedAlgHom K (a.algebra j) (c.domainCover.obj t).algebra :=
  (c.domainOverRightChart t).baseMap

/-- Compatibility follows from original algebra-map identities on a
finite common-chart refinement of every full-domain test. -/
theorem chartRestrictionFamily_compatible :
    c.domainCover.BoundedMapCompatible c.chartRestrictionFamily := by
  intro t s W p q
  change p.restriction.comp
      ((c.domainCoverToChart t).restriction.comp
        (a.restriction (c.index t) j (c.right_subset t))) =
    q.restriction.comp
      ((c.domainCoverToChart s).restriction.comp
        (a.restriction (c.index s) j (c.right_subset s)))
  erw [← BoundedAlgHom.comp_assoc, ← BoundedAlgHom.comp_assoc]
  exact a.originalChartRestriction_overlap i j (c.index t) (c.index s)
    (c.left_subset t) (c.right_subset t) (c.left_subset s) (c.right_subset s) W
    (p ≫ c.domainCoverToChart t) (q ≫ c.domainCoverToChart s)

/-- Glue the actual local structural maps into the unchanged algebra of U. -/
def glueChartRestriction : BoundedAlgHom K (a.algebra j) U.algebra :=
  c.domainCover.glueBoundedAlgHom c.chartRestrictionFamily
    c.chartRestrictionFamily_compatible

theorem restriction_comp_glueChartRestriction (t : Fin c.size) :
    (c.domainCover.map t).restriction.comp c.glueChartRestriction =
      c.chartRestrictionFamily t :=
  c.domainCover.restriction_comp_glueBoundedAlgHom _ _ t

/-- Each local map has the original ambient chart equation. -/
theorem chartRestrictionFamily_chart (t : Fin c.size)
    (y : BanachSpectrum (c.domainCover.obj t).algebra) :
    a.chart j (BanachSpectrum.comap
        (c.chartRestrictionFamily t).toBoundedRingHom y) =
      a.chart i ((c.domainCover.obj t).spectrumMap y) := by
  calc
    a.chart j (BanachSpectrum.comap
        (c.chartRestrictionFamily t).toBoundedRingHom y) =
        a.chart (c.index t) ((c.domainCoverToChart t).spectrumMap y) :=
      a.restriction_chart (c.index t) j (c.right_subset t)
        ((c.domainCoverToChart t).spectrumMap y)
    _ = a.chart i ((a.restrictionDomain (c.index t) i (c.left_subset t)).spectrumMap
        ((c.domainCoverToChart t).spectrumMap y)) :=
      (a.restriction_chart (c.index t) i (c.left_subset t) _).symm
    _ = a.chart i ((c.domainCover.obj t).spectrumMap y) :=
      congrArg (a.chart i) ((c.domainCoverToChart t).spectrumMap_over_base y)

/-- Exact cover equations and full-domain spectral injectivity recover
the ambient chart equation on every point of the unchanged domain algebra. -/
theorem glueChartRestriction_chart (x : BanachSpectrum U.algebra) :
    a.chart j (BanachSpectrum.comap c.glueChartRestriction.toBoundedRingHom x) =
      a.chart i (U.spectrumMap x) := by
  obtain ⟨t, ht⟩ := c.domainCover.covers (U.spectrumMap x) (U.represents.hasImageIn x)
  obtain ⟨y, hy⟩ := (c.domainCover.obj t).represents.2.1.symm ▸ ht
  have hxy : (c.domainCover.map t).spectrumMap y = x :=
    U.spectrumMap_injective (((c.domainCover.map t).spectrumMap_over_base y).trans hy)
  have heq :
      BanachSpectrum.comap c.glueChartRestriction.toBoundedRingHom
          ((c.domainCover.map t).spectrumMap y) =
        BanachSpectrum.comap (c.chartRestrictionFamily t).toBoundedRingHom y := by
    apply BanachSpectrum.ext
    intro b
    exact congrArg (fun q : BoundedAlgHom K (a.algebra j)
      (c.domainCover.obj t).algebra => y (q b))
      (c.restriction_comp_glueChartRestriction t)
  rw [← hxy, heq]
  exact (c.chartRestrictionFamily_chart t y).trans
    (congrArg (a.chart i) ((c.domainCover.map t).spectrumMap_over_base y)).symm

end CompactIntersectionChartCover

/-- The constructed bounded restriction from any original chart containing
the ambient image of a local full domain. No directedness is needed. -/
def domainChartRestriction (i j : a.Index) (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j)) :
    BoundedAlgHom K (a.algebra j) U.algebra :=
  (a.domainImageChartCover i j U h).glueChartRestriction

theorem domainChartRestriction_chart (i j : a.Index) (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j))
    (x : BanachSpectrum U.algebra) :
    a.chart j (BanachSpectrum.comap
        (a.domainChartRestriction i j U h).toBoundedRingHom x) =
      a.chart i (U.spectrumMap x) :=
  (a.domainImageChartCover i j U h).glueChartRestriction_chart x

end Langlands.Analytic.IndexedAffinoidAtlas
