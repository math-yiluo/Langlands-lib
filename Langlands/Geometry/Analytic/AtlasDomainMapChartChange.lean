import Langlands.Geometry.Analytic.AtlasDomainRestrictions
import Langlands.Geometry.Analytic.AtlasMapChartChangeCoherence

/-! # Full coefficient-test laws for local-domain chart restrictions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- The original domain structural map has the required chart image. -/
theorem domainBaseMap_image_chart (i j : a.Index) (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j))
    (x : BanachSpectrum U.algebra) :
    a.chart i (BanachSpectrum.comap U.baseMap.toBoundedRingHom x) ∈
      Set.range (a.chart j) :=
  h ⟨U.spectrumMap x, U.represents.hasImageIn x, rfl⟩

/-- The domain-cover construction equals the general chart-change construction
as a complete bounded map, by its equations on the actual finite domain cover. -/
theorem domainChartRestriction_eq_changeMapChart (i j : a.Index)
    (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j)) :
    a.domainChartRestriction i j U h =
      a.changeMapChart i j U.algebra U.baseMap (a.domainBaseMap_image_chart i j U h) := by
  let c := a.domainImageChartCover i j U h
  have hc := a.changeMapChart_isMapChartChange i j U.algebra U.baseMap
    (a.domainBaseMap_image_chart i j U h)
  apply BoundedAlgHom.ext
  intro b
  apply c.domainCover.algebra_ext_of_restrict_eq
  intro t
  have hfactor :
      (c.domainCoverToChart t).restriction.comp
          (a.restriction (c.index t) i (c.left_subset t)) =
        (c.domainCover.map t).restriction.comp U.baseMap :=
    (c.domainCoverToChart t).comp_baseMap.trans
      (c.domainCover.map t).comp_baseMap.symm
  have ht := hc (c.domainCover.obj t).algebra (c.domainCover.map t).restriction
    (c.index t) (c.left_subset t) (c.right_subset t)
    (c.domainCoverToChart t).restriction hfactor
  have heq :
      (c.domainCover.map t).restriction.comp (a.domainChartRestriction i j U h) =
        (c.domainCover.map t).restriction.comp
          (a.changeMapChart i j U.algebra U.baseMap
            (a.domainBaseMap_image_chart i j U h)) :=
    (c.restriction_comp_glueChartRestriction t).trans ht.symm
  exact congrArg (fun q : BoundedAlgHom K (a.algebra j)
    (c.domainCover.obj t).algebra => q b) heq

/-- Domain restrictions satisfy the universal law for every bounded coefficient
map, not just coefficient maps arising from inclusions of local domains. -/
theorem domainChartRestriction_isMapChartChange (i j : a.Index)
    (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j)) :
    a.IsMapChartChange i j U.algebra U.baseMap (a.domainChartRestriction i j U h) := by
  rw [a.domainChartRestriction_eq_changeMapChart i j U h]
  exact a.changeMapChart_isMapChartChange i j U.algebra U.baseMap
    (a.domainBaseMap_image_chart i j U h)

/-- Changing a domain restriction to a third containing chart is defined
on the unchanged domain algebra. -/
def changeDomainChartRestriction (i j k : a.Index) (U : Domain K (a.algebra i))
    (hj : a.chart i '' U.locus ⊆ Set.range (a.chart j))
    (hk : a.chart i '' U.locus ⊆ Set.range (a.chart k)) :
    BoundedAlgHom K (a.algebra k) U.algebra :=
  a.changeMapChart j k U.algebra (a.domainChartRestriction i j U hj) (by
    intro x
    rw [a.domainChartRestriction_chart i j U hj x]
    exact a.domainBaseMap_image_chart i k U hk x)

/-- The iterated construction recovers the direct domain restriction in full. -/
theorem changeDomainChartRestriction_eq (i j k : a.Index)
    (U : Domain K (a.algebra i))
    (hj : a.chart i '' U.locus ⊆ Set.range (a.chart j))
    (hk : a.chart i '' U.locus ⊆ Set.range (a.chart k)) :
    a.changeDomainChartRestriction i j k U hj hk = a.domainChartRestriction i k U hk := by
  unfold changeDomainChartRestriction
  simp only [a.domainChartRestriction_eq_changeMapChart i j U hj,
    a.domainChartRestriction_eq_changeMapChart i k U hk]
  exact a.changeMapChart_trans i j k U.algebra U.baseMap
    (a.domainBaseMap_image_chart i j U hj) (a.domainBaseMap_image_chart i k U hk) _

/-- Any two containing charts give a universally compatible pair of domain
restrictions, including after every bounded affinoid coefficient change. -/
theorem domainChartRestriction_pair_isMapChartChange (i j k : a.Index)
    (U : Domain K (a.algebra i))
    (hj : a.chart i '' U.locus ⊆ Set.range (a.chart j))
    (hk : a.chart i '' U.locus ⊆ Set.range (a.chart k)) :
    a.IsMapChartChange j k U.algebra
      (a.domainChartRestriction i j U hj) (a.domainChartRestriction i k U hk) := by
  rw [← a.changeDomainChartRestriction_eq i j k U hj hk]
  exact a.changeMapChart_isMapChartChange j k U.algebra
    (a.domainChartRestriction i j U hj) _

/-- Every local-domain inclusion retains universal chart-change compatibility
between the structural maps of its two original parent charts. -/
theorem domainRestriction_isMapChartChange (i j : a.Index)
    (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus) :
    a.IsMapChartChange i j U.algebra U.baseMap
      ((a.domainRestriction i j U V h).comp V.baseMap) := by
  rw [a.domainRestriction_comp_baseMap i j U V h]
  exact a.domainChartRestriction_isMapChartChange i j U _

end Langlands.Analytic.IndexedAffinoidAtlas
