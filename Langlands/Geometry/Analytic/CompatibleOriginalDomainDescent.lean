import Langlands.Geometry.Analytic.OriginalDomainRefinedStrongDescent
import Langlands.Geometry.Analytic.CompatibleDomainRestriction
import Langlands.Geometry.Analytic.CompatibleStrongSubatlasRefinement
import Langlands.Geometry.Analytic.SaturatedDomainCorestriction

/-! # Compatible full-map descent after an actual source refinement -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AffinoidAtlasPresentation

open Set CategoryTheory IndexedAffinoidAtlas.OriginalChartDomain
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}

namespace CompatibleStrongHom

/-- Restriction between actual original source domains retains full coefficient coherence. -/
def restrictOriginalDomain {S T : A.atlas.OriginalChartDomain}
    (f : CompatibleStrongHom (A.originalDomainPresentation T) B) (hST : S ≤ T) :
    CompatibleStrongHom (A.originalDomainPresentation S) B where
  toStrongHom := f.toStrongHom.restrictOriginalDomain hST
  compatible := StrongHom.hasLocallyCompatiblePullbacks_iff _ |>.mpr (by
    intro c j k hj hk
    exact f.coherent ⟨c.val, c.property.trans hST⟩ j k
      ((StrongHom.restrictOriginalDomain_admissible_iff hST f.toStrongHom c j).mp hj)
      ((StrongHom.restrictOriginalDomain_admissible_iff hST f.toStrongHom c k).mp hk))

/-- Direct source-domain restriction preserves entire compatible composites. -/
theorem restrictOriginalDomain_comp {S T : A.atlas.OriginalChartDomain}
    (f : CompatibleStrongHom (A.originalDomainPresentation T) B) (g : CompatibleStrongHom B C)
    (hST : S ≤ T) :
    (f.comp g).restrictOriginalDomain hST = (f.restrictOriginalDomain hST).comp g := by
  refine CompatibleStrongHom.ext_of_pullback rfl fun c => ?_
  let d : A.atlas.SubspaceChart T.carrier := ⟨c.val, c.property.trans hST⟩
  obtain ⟨j, hfj⟩ := f.target_exists d
  obtain ⟨k, hgk⟩ := g.target_exists j
  have hfr : (f.restrictOriginalDomain hST).baseMap ''
      range ((A.originalDomainPresentation S).atlas.chart c) ⊆ range (B.atlas.chart j) :=
    (StrongHom.restrictOriginalDomain_admissible_iff hST f.toStrongHom c j).mpr hfj
  have hc := (f.restrictOriginalDomain hST).toStrongHom.comp_admissible g.toStrongHom c j k hfr hgk
  have hfg := f.toStrongHom.comp_admissible g.toStrongHom d j k hfj hgk
  refine ⟨k, hc, ?_⟩
  change (f.comp g).pullback d k hfg = ((f.restrictOriginalDomain hST).comp g).pullback c k hc
  erw [CompatibleStrongHom.comp_pullback f g d j k hfj hgk,
    CompatibleStrongHom.comp_pullback (f.restrictOriginalDomain hST) g c j k hfr hgk]
  rfl

/-- Two source restrictions compose to the direct original subspace restriction. -/
theorem restrictSubspace_restrictOriginalDomain (f : CompatibleStrongHom A B)
    {S T : A.atlas.OriginalChartDomain} (hST : S ≤ T) :
    (f.restrictSubspace T.carrier T.is_domain).restrictOriginalDomain hST =
      f.restrictSubspace S.carrier S.is_domain :=
  CompatibleStrongHom.ext (f.toStrongHom.restrictSubspace_restrictOriginalDomain hST)

end CompatibleStrongHom

namespace OriginalDomainStrongMatchingFamily

variable {ι : Type z} {D : ι → A.atlas.OriginalChartDomain}
  (d : OriginalDomainStrongMatchingFamily A B D) (hA : A.atlas.HasAllLocalDomains)

/-- Full local maps have their canonical compatible structure from source saturation. -/
def compatibleLocalMap (k : ι) : CompatibleStrongHom (A.originalDomainPresentation (D k)) B :=
  CompatibleStrongHom.ofSaturated (d.localMap k)
    (IndexedAffinoidAtlas.subspaceAtlas_hasAllLocalDomains hA _ (D k).is_domain)

/-- Full matching families give actual compatible global maps on the constructed
same-space source refinement. All local-domain closure is proved. -/
def compatibleRefinedGlue
    (hD : AtlasTopology.LocallyRefines (range (fun k => (D k).carrier)) {univ}) :
    CompatibleStrongHom (A.refiningSubpresentation (domainCoverSourceSelection D hD)) B :=
  CompatibleStrongHom.ofSaturated (d.refinedGlue hD)
    (A.atlas.subatlas_hasAllLocalDomains hA _
      (domainCoverSourceSelection D hD).locally_refining
      (domainCoverSourceSelection D hD).downward_closed)

/-- The constructed map retains each complete local point map. -/
theorem compatibleRefinedGlue_apply
    (hD : AtlasTopology.LocallyRefines (range (fun k => (D k).carrier)) {univ})
    (k : ι) (x : (D k).carrier) :
    (d.compatibleRefinedGlue hA hD).baseMap x.val = (d.localMap k).baseMap x :=
  congrArg (fun q => q.baseMap x) (d.refinedGlue_restrictSubspace hD k)

/-- Every selected source chart inside a cover member retains its entire
original local bounded pullback under the actual gluing. -/
theorem compatibleRefinedGlue_pullback
    (hD : AtlasTopology.LocallyRefines (range (fun k => (D k).carrier)) {univ})
    (k : ι) (c : (A.refiningSubpresentation (domainCoverSourceSelection D hD)).atlas.Index)
    (hck : range (A.atlas.chart c.val) ⊆ (D k).carrier) (j : B.atlas.Index)
    (hg : (d.compatibleRefinedGlue hA hD).baseMap '' range (A.atlas.chart c.val) ⊆ range (B.atlas.chart j))
    (hl : (d.localMap k).baseMap '' range ((A.originalDomainPresentation (D k)).atlas.chart ⟨c.val, hck⟩) ⊆
      range (B.atlas.chart j)) :
    (d.compatibleRefinedGlue hA hD).pullback c j hg = (d.localMap k).pullback ⟨c.val, hck⟩ j hl := by
  let c' : (A.subpresentation (domainCoverSourceSelection D hD).carrier
      (domainCoverSourceSelection D hD).locally_refining).atlas.SubspaceChart (D k).carrier := ⟨c, hck⟩
  exact StrongHom.pullback_congr (d.refinedGlue_restrictSubspace hD k) c' j
    (((d.refinedGlue hD).restrictSubspace_admissible_iff (D k).carrier _ c' j).mpr hg) hl

/-- Gluing a compatible local cone preserves a complete projection exactly,
including its original bounded maps on the selected source charts. -/
theorem compatibleRefinedGlue_comp
    (hD : AtlasTopology.LocallyRefines (range (fun k => (D k).carrier)) {univ})
    (p : CompatibleStrongHom B C) (f : CompatibleStrongHom A C)
    (hlocal : ∀ k, (d.compatibleLocalMap hA k).comp p =
      f.restrictSubspace (D k).carrier (D k).is_domain) :
    (d.compatibleRefinedGlue hA hD).comp p =
      f.restrictSubatlasSource (domainCoverSourceSelection D hD).carrier
        (domainCoverSourceSelection D hD).locally_refining := by
  let G := d.compatibleRefinedGlue hA hD
  have hb : (G.comp p).baseMap =
      (f.restrictSubatlasSource (domainCoverSourceSelection D hD).carrier
        (domainCoverSourceSelection D hD).locally_refining).baseMap := by
    apply ContinuousMap.ext
    intro x
    obtain ⟨σ, -, hs, hm, hn⟩ := hD univ (mem_singleton _) x (mem_univ x)
    have hnh : ⋃₀ σ ∈ 𝓝 x := by
      change ⋃₀ σ ∈ 𝓝[univ] x at hn
      rwa [nhdsWithin_univ] at hn
    have hx : x ∈ ⋃₀ σ := mem_of_mem_nhds hnh
    obtain ⟨F, hF, hxF⟩ := hx
    obtain ⟨k, hk⟩ := hs hF
    change (D k).carrier = F at hk
    have hxD : x ∈ (D k).carrier := hk.symm ▸ hxF
    have he := congrArg (fun q => q.baseMap (⟨x, hxD⟩ : (D k).carrier)) (hlocal k)
    change p.baseMap (G.baseMap x) = f.baseMap x
    exact (congrArg p.baseMap (d.compatibleRefinedGlue_apply hA hD k ⟨x, hxD⟩)).trans he
  refine CompatibleStrongHom.ext_of_pullback hb fun c => ?_
  obtain ⟨k, hck, -⟩ := c.property
  let e : A.atlas.SubspaceChart (D k).carrier := ⟨c.val, hck⟩
  let L := d.compatibleLocalMap hA k
  obtain ⟨J, hLJ⟩ := L.target_exists e
  obtain ⟨j, hpj⟩ := p.target_exists J
  have hGJ : G.baseMap '' range (A.atlas.chart c.val) ⊆ range (B.atlas.chart J) := by
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    have he := d.compatibleRefinedGlue_apply hA hD k ⟨A.atlas.chart c.val s, hck ⟨s, rfl⟩⟩
    exact he.symm ▸ hLJ ⟨_, ⟨s, rfl⟩, rfl⟩
  have hGj := G.toStrongHom.comp_admissible p.toStrongHom c J j hGJ hpj
  have hLj := L.toStrongHom.comp_admissible p.toStrongHom e J j hLJ hpj
  have hfj : f.baseMap '' range (A.atlas.chart c.val) ⊆ range (C.atlas.chart j) := by
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    have he := congrArg (fun q => q.baseMap ((A.originalDomainPresentation (D k)).atlas.chart e s))
      (hlocal k)
    exact he ▸ hLj ⟨_, ⟨s, rfl⟩, rfl⟩
  have hfl : (f.restrictSubspace (D k).carrier (D k).is_domain).baseMap ''
      range ((A.originalDomainPresentation (D k)).atlas.chart e) ⊆ range (C.atlas.chart j) := by
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    exact hfj ⟨_, ⟨s, rfl⟩, rfl⟩
  refine ⟨j, hGj, ?_⟩
  change (G.comp p).pullback c j hGj = f.pullback c.val j hfj
  exact (CompatibleStrongHom.comp_pullback G p c J j hGJ hpj hGj).trans
    ((congrArg (fun q => q.comp (p.pullback J j hpj))
      (d.compatibleRefinedGlue_pullback hA hD k c hck J hGJ hLJ)).trans
      ((CompatibleStrongHom.comp_pullback L p e J j hLJ hpj hLj).symm.trans
        (StrongHom.pullback_congr (congrArg CompatibleStrongHom.toStrongHom (hlocal k))
          e j hLj hfl)))

end OriginalDomainStrongMatchingFamily

end Langlands.Analytic.AffinoidAtlasPresentation
