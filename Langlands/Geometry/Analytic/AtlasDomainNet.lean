import Langlands.Geometry.Analytic.AtlasDomainCategory
import Langlands.Geometry.Analytic.AtlasTopology.DomainIntersections

/-! # The net of all actual local full affinoid domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra Filter Topology
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Original-chart localization preserves the exact ambient subset. -/
theorem chart_image_restrictDomain (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (V : Domain K (a.algebra j)) (f : V ⟶ a.restrictionDomain i j h) :
    a.chart i '' (a.restrictDomain i j h V f).locus = a.chart j '' V.locus := by
  rw [← a.chart_image_extendDomain_locus i j h (a.restrictDomain i j h V f)]
  exact congrArg (fun S : Set (BanachSpectrum (a.algebra j)) => a.chart j '' S)
    (a.extend_restrictDomain_locus i j h V f)

theorem chart_image_inter_restrictionDomain (i m : a.Index)
    (h : Set.range (a.chart m) ⊆ Set.range (a.chart i))
    (U : Domain K (a.algebra i)) :
    a.chart i '' (U.inter (a.restrictionDomain m i h)).locus =
      (a.chart i '' U.locus) ∩ Set.range (a.chart m) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hm⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, hm⟩
  · rintro ⟨⟨y, hy, rfl⟩, hm⟩
    exact ⟨y, ⟨hy, hm⟩, rfl⟩

namespace LocalDomain

variable {a}

/-- The actual full intersection with a common original chart, localized
through its original second quotient projection. -/
def partInChart (U : LocalDomain a) (m : a.Index)
    (h : Set.range (a.chart m) ⊆ Set.range (a.chart U.index)) :
    Domain K (a.algebra m) :=
  a.restrictDomain m U.index h (U.domain.inter (a.restrictionDomain m U.index h))
    (Domain.interRight U.domain (a.restrictionDomain m U.index h))

theorem chart_image_partInChart (U : LocalDomain a) (m : a.Index)
    (h : Set.range (a.chart m) ⊆ Set.range (a.chart U.index)) :
    a.chart m '' (U.partInChart m h).locus = U.locus ∩ Set.range (a.chart m) :=
  (a.chart_image_restrictDomain m U.index h _ _).trans
    (a.chart_image_inter_restrictionDomain U.index m h U.domain)

/-- An actual common-chart full domain inside the intersection of two
arbitrary original local-domain presentations. -/
def interInChart (U V : LocalDomain a) (m : a.Index)
    (hU : Set.range (a.chart m) ⊆ Set.range (a.chart U.index))
    (hV : Set.range (a.chart m) ⊆ Set.range (a.chart V.index)) : LocalDomain a :=
  ⟨m, (U.partInChart m hU).inter (V.partInChart m hV)⟩

theorem interInChart_locus (U V : LocalDomain a) (m : a.Index)
    (hU : Set.range (a.chart m) ⊆ Set.range (a.chart U.index))
    (hV : Set.range (a.chart m) ⊆ Set.range (a.chart V.index)) :
    (U.interInChart V m hU hV).locus = (U.locus ∩ V.locus) ∩ Set.range (a.chart m) := by
  change a.chart m '' ((U.partInChart m hU).locus ∩ (V.partInChart m hV).locus) = _
  rw [Set.image_inter (a.isEmbedding_chart m).injective,
    U.chart_image_partInChart m hU, V.chart_image_partInChart m hV]
  ext x
  simp only [Set.mem_inter_iff]
  tauto

end LocalDomain

/-- All subsets represented as full domains in any one original chart. -/
def localDomainFamily : Set (Set X) := Set.range (LocalDomain.locus (a := a))

theorem chartFamily_subset_localDomainFamily :
    Set.range (fun i => Set.range (a.chart i)) ⊆ a.localDomainFamily := by
  rintro _ ⟨i, rfl⟩
  refine ⟨⟨i, Domain.whole K (a.algebra i)⟩, ?_⟩
  exact Set.image_univ

theorem isQuasinet_localDomainFamily : AtlasTopology.IsQuasinet a.localDomainFamily :=
  a.isNet_chartFamily.1.mono a.chartFamily_subset_localDomainFamily

/-- Every intersection of local domains has finite relative neighborhoods
of actual local domains constructed in common original charts. -/
theorem localDomainFamily_locallyRefines_intersection (U V : LocalDomain a) :
    AtlasTopology.LocallyRefines a.localDomainFamily {U.locus ∩ V.locus} := by
  rintro S hS x hx
  have hS' : S = U.locus ∩ V.locus := Set.mem_singleton_iff.mp hS
  subst S
  have hsub : U.locus ∩ V.locus ⊆
      Set.range (a.chart U.index) ∩ Set.range (a.chart V.index) := by
    rintro y ⟨⟨u, _, hu⟩, ⟨v, _, hv⟩⟩
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  obtain ⟨σ, hf, hs, hm, hn⟩ :=
    (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp
      (a.isNet_chartFamily.2 _ (Set.mem_range_self U.index) _
        (Set.mem_range_self V.index)) _ (Set.mem_singleton _) x (hsub hx)
  classical
  let := hf.fintype
  choose k hk using fun W : σ => hs W.property
  change ∀ W : σ, Set.range (a.chart (k W)) = W.val at hk
  have hkU (W : σ) : Set.range (a.chart (k W)) ⊆ Set.range (a.chart U.index) := by
    rw [hk W]
    exact fun _ hy => ((hm W.val W.property).1 hy).1
  have hkV (W : σ) : Set.range (a.chart (k W)) ⊆ Set.range (a.chart V.index) := by
    rw [hk W]
    exact fun _ hy => ((hm W.val W.property).1 hy).2
  let Z (W : σ) := U.interInChart V (k W) (hkU W) (hkV W)
  have hZ (W : σ) : (Z W).locus = (U.locus ∩ V.locus) ∩ W.val := by
    change (U.interInChart V (k W) (hkU W) (hkV W)).locus = _
    rw [LocalDomain.interInChart_locus, hk W]
  refine ⟨Set.range (fun W : σ => (Z W).locus), Set.finite_range _, ?_, ?_, ?_⟩
  · rintro _ ⟨W, rfl⟩
    exact ⟨Z W, rfl⟩
  · rintro _ ⟨W, rfl⟩
    change (Z W).locus ⊆ U.locus ∩ V.locus ∧ x ∈ (Z W).locus
    rw [hZ W]
    exact ⟨Set.inter_subset_left, hx, (hm W.val W.property).2⟩
  · apply Filter.mem_of_superset
      (inter_mem self_mem_nhdsWithin ((nhdsWithin_mono x hsub) hn))
    rintro y ⟨hy, W, hW, hyW⟩
    refine ⟨(Z ⟨W, hW⟩).locus, ⟨⟨W, hW⟩, rfl⟩, ?_⟩
    rw [hZ ⟨W, hW⟩]
    exact ⟨hy, hyW⟩

/-- Berkovich's enlarged local-affinoid family is an actual net. -/
theorem isNet_localDomainFamily : AtlasTopology.IsNet a.localDomainFamily := by
  refine ⟨a.isQuasinet_localDomainFamily, ?_⟩
  rintro _ ⟨U, rfl⟩ _ ⟨V, rfl⟩
  exact (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mpr
    (a.localDomainFamily_locallyRefines_intersection U V)

theorem isCompactFamily_localDomainFamily : AtlasTopology.IsCompactFamily a.localDomainFamily := by
  rintro _ ⟨U, rfl⟩
  exact ⟨U.isCompact_locus, U.locusHomeomorph.t2Space⟩

end Langlands.Analytic.IndexedAffinoidAtlas
