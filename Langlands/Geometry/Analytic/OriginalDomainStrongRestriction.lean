import Langlands.Geometry.Analytic.OriginalDomainStrongPresheaf
import Langlands.Geometry.Analytic.StrongAtlasQuasiIsomorphisms

/-! # Full strong maps restricted to actual source and target domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open Set Topology CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

namespace StrongHom

/-- Every original source chart contained in S maps into an original target
chart contained in T. This is a chartwise condition on the ambient map. -/
def MapsOriginalDomainCharts (f : StrongHom A B)
    (S : A.atlas.OriginalChartDomain) (T : B.atlas.OriginalChartDomain) : Prop :=
  ∀ c : A.atlas.SubspaceChart S.carrier,
    ∃ d : B.atlas.SubspaceChart T.carrier,
      f.baseMap '' Set.range (A.atlas.chart c.val) ⊆ Set.range (B.atlas.chart d.val)

/-- Actual point containment follows from chart witnesses and the net
covering the constructed source domain. -/
theorem MapsOriginalDomainCharts.mapsTo {f : StrongHom A B}
    {S : A.atlas.OriginalChartDomain} {T : B.atlas.OriginalChartDomain}
    (h : f.MapsOriginalDomainCharts S T) :
    Set.MapsTo f.baseMap S.carrier T.carrier := by
  intro x hx
  have hx' : (⟨x, hx⟩ : S.carrier) ∈ ⋃₀ Set.range
      (fun c => Set.range ((A.originalDomainPresentation S).atlas.chart c)) := by
    rw [(A.originalDomainPresentation S).atlas.isNet_chartFamily.1.covers]
    trivial
  obtain ⟨_, ⟨c, rfl⟩, y, hy⟩ := Set.mem_sUnion.mp hx'
  obtain ⟨d, hd⟩ := h c
  have hxy : A.atlas.chart c.val y = x := congrArg Subtype.val hy
  exact d.property (hd ⟨x, ⟨y, hxy⟩, rfl⟩)

/-- Smaller source domains retain the same contained-target-chart witnesses. -/
theorem MapsOriginalDomainCharts.mono_source {f : StrongHom A B}
    {S S' : A.atlas.OriginalChartDomain} {T : B.atlas.OriginalChartDomain}
    (h : f.MapsOriginalDomainCharts S T) (hS : S' ≤ S) :
    f.MapsOriginalDomainCharts S' T :=
  fun c => h ⟨c.val, c.property.trans hS⟩

/-- Enlarging the target domain retains the actual target charts. -/
theorem MapsOriginalDomainCharts.mono_target {f : StrongHom A B}
    {S : A.atlas.OriginalChartDomain} {T T' : B.atlas.OriginalChartDomain}
    (h : f.MapsOriginalDomainCharts S T) (hT : T ≤ T') :
    f.MapsOriginalDomainCharts S T' := by
  intro c
  obtain ⟨d, hd⟩ := h c
  exact ⟨⟨d.val, d.property.trans hT⟩, hd⟩

/-- Restrict the actual continuous map to both domain subspaces. -/
def restrictDomainsBaseMap (f : StrongHom A B)
    (S : A.atlas.OriginalChartDomain) (T : B.atlas.OriginalChartDomain)
    (h : f.MapsOriginalDomainCharts S T) : C(S.carrier, T.carrier) :=
  ⟨fun x => ⟨f.baseMap x.val, h.mapsTo x.property⟩,
    (f.baseMap.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- Subspace admissibility is exactly ambient admissibility at the same
original source and target charts. -/
theorem restrictDomainsBaseMap_admissible_iff (f : StrongHom A B)
    (S : A.atlas.OriginalChartDomain) (T : B.atlas.OriginalChartDomain)
    (h : f.MapsOriginalDomainCharts S T)
    (c : A.atlas.SubspaceChart S.carrier) (d : B.atlas.SubspaceChart T.carrier) :
    (f.restrictDomainsBaseMap S T h) ''
        Set.range ((A.originalDomainPresentation S).atlas.chart c) ⊆
          Set.range ((B.originalDomainPresentation T).atlas.chart d) ↔
      f.baseMap '' Set.range (A.atlas.chart c.val) ⊆ Set.range (B.atlas.chart d.val) := by
  constructor <;> intro hc <;> rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  · obtain ⟨y, hy⟩ := hc ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · obtain ⟨y, hy⟩ := hc ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨y, Subtype.ext hy⟩

/-- Restrict a full strong map to two actual original-chart domains,
retaining every ambient admissible bounded pullback. -/
def restrictDomains (f : StrongHom A B)
    (S : A.atlas.OriginalChartDomain) (T : B.atlas.OriginalChartDomain)
    (h : f.MapsOriginalDomainCharts S T) :
    StrongHom (A.originalDomainPresentation S) (B.originalDomainPresentation T) where
  baseMap := f.restrictDomainsBaseMap S T h
  target_exists c := by
    obtain ⟨d, hd⟩ := h c
    exact ⟨d, (f.restrictDomainsBaseMap_admissible_iff S T h c d).mpr hd⟩
  pullback c d hc := f.pullback c.val d.val
    ((f.restrictDomainsBaseMap_admissible_iff S T h c d).mp hc)
  chart_comm c d hc x := Subtype.ext (f.chart_comm c.val d.val _ x)
  restriction_comm c c' d d' hc hd hcd hc'd' :=
    f.restriction_comm c.val c'.val d.val d'.val
      (A.atlas.chart_subset_of_subspaceSubset S.carrier c c' hc)
      (B.atlas.chart_subset_of_subspaceSubset T.carrier d d' hd)
      ((f.restrictDomainsBaseMap_admissible_iff S T h c d).mp hcd)
      ((f.restrictDomainsBaseMap_admissible_iff S T h c' d').mp hc'd')

@[simp]
theorem restrictDomains_apply_val (f : StrongHom A B)
    (S : A.atlas.OriginalChartDomain) (T : B.atlas.OriginalChartDomain)
    (h : f.MapsOriginalDomainCharts S T) (x : S.carrier) :
    ((f.restrictDomains S T h).baseMap x).val = f.baseMap x.val := rfl

/-- This compares entire bounded algebra homomorphisms, including all data
not detected by spectrum-point values. -/
theorem restrictDomains_pullback (f : StrongHom A B)
    (S : A.atlas.OriginalChartDomain) (T : B.atlas.OriginalChartDomain)
    (h : f.MapsOriginalDomainCharts S T)
    (c : A.atlas.SubspaceChart S.carrier) (d : B.atlas.SubspaceChart T.carrier)
    (hc : (f.restrictDomains S T h).baseMap ''
      Set.range ((A.originalDomainPresentation S).atlas.chart c) ⊆
        Set.range ((B.originalDomainPresentation T).atlas.chart d)) :
    (f.restrictDomains S T h).pullback c d hc =
      f.pullback c.val d.val
        ((f.restrictDomainsBaseMap_admissible_iff S T h c d).mp hc) := rfl

/-- Source restriction commutes as equality of full strong maps. -/
theorem restrictDomains_restrictOriginalDomain (f : StrongHom A B)
    {S S' : A.atlas.OriginalChartDomain} (T : B.atlas.OriginalChartDomain)
    (h : f.MapsOriginalDomainCharts S T) (hS : S' ≤ S) :
    (f.restrictDomains S T h).restrictOriginalDomain hS =
      f.restrictDomains S' T (h.mono_source hS) := by
  refine ext_of_pullback rfl ?_
  intro c d hc hc'
  rfl

/-- Local image loci in target-chart spectrum coordinates are unchanged. -/
theorem restrictDomains_chartImageLocus (f : StrongHom A B)
    (S : A.atlas.OriginalChartDomain) (T : B.atlas.OriginalChartDomain)
    (h : f.MapsOriginalDomainCharts S T)
    (c : A.atlas.SubspaceChart S.carrier) (d : B.atlas.SubspaceChart T.carrier) :
    (f.restrictDomains S T h).chartImageLocus c d =
      f.chartImageLocus c.val d.val := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, hx⟩
    exact ⟨_, ⟨x, rfl⟩, congrArg Subtype.val hx⟩
  · rintro ⟨_, ⟨x, rfl⟩, hx⟩
    exact ⟨_, ⟨x, rfl⟩, Subtype.ext hx⟩

/-- A strong quasi-isomorphism restricts to a strong quasi-isomorphism
when it carries the chosen source domain exactly onto the target domain. -/
theorem IsQuasiIso.restrictDomains {f : StrongHom A B} (hf : f.IsQuasiIso)
    (S : A.atlas.OriginalChartDomain) (T : B.atlas.OriginalChartDomain)
    (h : f.MapsOriginalDomainCharts S T)
    (himage : f.baseMap '' S.carrier = T.carrier) :
    (f.restrictDomains S T h).IsQuasiIso := by
  refine ⟨?_, ?_⟩
  · exact ((hf.1.homeomorph.image S.carrier).trans (Homeomorph.setCongr himage)).isHomeomorph
  · intro c d hc
    rw [f.restrictDomains_chartImageLocus S T h c d]
    exact hf.2 c.val d.val ((f.restrictDomainsBaseMap_admissible_iff S T h c d).mp hc)

/-- The ambient identity supplies the chart witnesses for nested domains. -/
theorem mapsOriginalDomainCharts_id {S T : A.atlas.OriginalChartDomain} (hST : S ≤ T) :
    (StrongHom.id A).MapsOriginalDomainCharts S T := by
  intro c
  exact ⟨⟨c.val, c.property.trans hST⟩, fun _ ⟨x, hx, hxy⟩ => hxy ▸ hx⟩

@[simp]
theorem restrictDomains_id (S : A.atlas.OriginalChartDomain)
    (h : (StrongHom.id A).MapsOriginalDomainCharts S S) :
    (StrongHom.id A).restrictDomains S S h = StrongHom.id (A.originalDomainPresentation S) := by
  refine ext_of_pullback rfl ?_
  intro c d hc hc'
  rfl

end StrongHom

/-- The full strong inclusion between nested original-chart domains has every
admissible original bounded restriction, without a directed target atlas. -/
def originalDomainStrongMap {S T : A.atlas.OriginalChartDomain} (hST : S ≤ T) :
    StrongHom (A.originalDomainPresentation S) (A.originalDomainPresentation T) :=
  (StrongHom.id A).restrictDomains S T (StrongHom.mapsOriginalDomainCharts_id hST)

@[simp]
theorem originalDomainStrongMap_apply_val {S T : A.atlas.OriginalChartDomain}
    (hST : S ≤ T) (x : S.carrier) :
    ((originalDomainStrongMap (A := A) hST).baseMap x).val = x.val := rfl

/-- Every admissible local map is the original bounded atlas restriction. -/
theorem originalDomainStrongMap_pullback {S T : A.atlas.OriginalChartDomain}
    (hST : S ≤ T) (c : A.atlas.SubspaceChart S.carrier)
    (d : A.atlas.SubspaceChart T.carrier)
    (h : (originalDomainStrongMap (A := A) hST).baseMap ''
      Set.range ((A.originalDomainPresentation S).atlas.chart c) ⊆
        Set.range ((A.originalDomainPresentation T).atlas.chart d)) :
    (originalDomainStrongMap (A := A) hST).pullback c d h =
      A.atlas.restriction c.val d.val
        (fun x hx => ((StrongHom.id A).restrictDomainsBaseMap_admissible_iff
          S T (StrongHom.mapsOriginalDomainCharts_id hST) c d).mp h ⟨x, hx, rfl⟩) := rfl

/-- At the chosen target copy of each source chart, the full map recovers
the bounded identity of the existing chosen domain inclusion. -/
theorem originalDomainStrongMap_pullback_selected {S T : A.atlas.OriginalChartDomain}
    (hST : S ≤ T) (c : A.atlas.SubspaceChart S.carrier)
    (h : (originalDomainStrongMap (A := A) hST).baseMap ''
      Set.range ((A.originalDomainPresentation S).atlas.chart c) ⊆
        Set.range ((A.originalDomainPresentation T).atlas.chart
          ⟨c.val, c.property.trans hST⟩)) :
    (originalDomainStrongMap (A := A) hST).pullback c
        ⟨c.val, c.property.trans hST⟩ h =
      (A.originalDomainMap hST).pullback c :=
  A.atlas.restriction_id c.val _

/-- A further direct source restriction gives the direct full inclusion. -/
theorem originalDomainStrongMap_restrict {S T U : A.atlas.OriginalChartDomain}
    (hST : S ≤ T) (hTU : T ≤ U) :
    (originalDomainStrongMap (A := A) hTU).restrictOriginalDomain hST =
      originalDomainStrongMap (A := A) (hST.trans hTU) := by
  refine StrongHom.ext_of_pullback rfl ?_
  intro c d hc hc'
  rfl

@[simp]
theorem originalDomainStrongMap_id (S : A.atlas.OriginalChartDomain) :
    originalDomainStrongMap (A := A) (le_refl S) =
      StrongHom.id (A.originalDomainPresentation S) :=
  StrongHom.restrictDomains_id S _

end Langlands.Analytic.AffinoidAtlasPresentation
