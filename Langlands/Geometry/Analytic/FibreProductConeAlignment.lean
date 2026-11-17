import Langlands.Geometry.Analytic.FibreProductLocalCharts
import Langlands.Geometry.Analytic.CompatibleStrongSubatlasRefinement

/-! # Source refinements aligning full cones with good pair charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology Filter PresentedAffinoidAlgebra AffinoidAtlasPresentation
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (d : IndexedAffinoidAtlas.{u, v, w} K X)

/-- An original chart whose range lies in an open Hausdorff subspace. -/
def HasOpenHausdorffContainer (i : d.Index) : Prop :=
  ∃ U : Set X, IsOpen U ∧ T2Space U ∧ range (d.chart i) ⊆ U

theorem hasOpenHausdorffContainer_downward : d.IsDownwardClosedSelection d.HasOpenHausdorffContainer := by
  rintro i j hij ⟨U, hU, hUT, hj⟩
  exact ⟨U, hU, hUT, hij.trans hj⟩

/-- Domain saturation refines every original chart locally by charts
contained in open Hausdorff patches. -/
theorem hasOpenHausdorffContainer_locallyRefining (hd : d.HasAllLocalDomains) :
    d.IsLocallyRefiningSelection d.HasOpenHausdorffContainer := by
  rintro _ ⟨i, rfl⟩ x hx
  obtain ⟨U, hU, hxU, hUT⟩ := FibreProduct.exists_open_hausdorff_neighborhood d x
  obtain ⟨j, hj, hxj, hjN⟩ := d.exists_subchart_nhdsWithin_open hd hU i hx hxU
  refine ⟨{range (d.chart j)}, finite_singleton _, singleton_subset_iff.mpr
    ⟨⟨j, U, hU, hUT, hj.trans inter_subset_right⟩, rfl⟩, ?_, ?_⟩
  · intro V hV
    rcases mem_singleton_iff.mp hV with rfl
    exact ⟨hj.trans inter_subset_left, hxj⟩
  · simpa only [sUnion_singleton] using hjN

end IndexedAffinoidAtlas

namespace FibreProduct

variable {A B C T : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)
  (a : CompatibleStrongHom T A) (b : CompatibleStrongHom T B)

/-- Original source charts whose two cone images lie in the two factor
charts of one good pair with an actual original common base. -/
def alignedSourceCharts (i : T.atlas.Index) : Prop :=
  ∃ p ∈ goodPairs f g, a.baseMap '' range (T.atlas.chart i) ⊆ range (A.atlas.chart p.val.1) ∧
    b.baseMap '' range (T.atlas.chart i) ⊆ range (B.atlas.chart p.val.2)

theorem alignedSourceCharts_downward :
    T.atlas.IsDownwardClosedSelection (alignedSourceCharts f g a b) := by
  rintro i j hij ⟨p, hp, ha, hb⟩
  exact ⟨p, hp, (image_mono hij).trans ha, (image_mono hij).trans hb⟩

/-- A commuting complete cone admits a locally refining selection aligned
with actual good pair charts. The base atlas is not assumed Hausdorff. -/
theorem alignedSourceCharts_locallyRefining
    (hT : T.atlas.HasAllLocalDomains) (hA : A.atlas.HasAllLocalDomains)
    (hB : B.atlas.HasAllLocalDomains) (hab : a.comp f = b.comp g) :
    T.atlas.IsLocallyRefiningSelection (alignedSourceCharts f g a b) := by
  classical
  let PA := A.atlas.HasOpenHausdorffContainer
  let PB := B.atlas.HasOpenHausdorffContainer
  have hPA := A.atlas.hasOpenHausdorffContainer_locallyRefining hA
  have hPB := B.atlas.hasOpenHausdorffContainer_locallyRefining hB
  have hSA := a.toStrongHom.sourceSelectionForTarget_locallyRefining hT PA hPA
  have hSB := b.toStrongHom.sourceSelectionForTarget_locallyRefining hT PB hPB
  have hdSA : T.atlas.IsDownwardClosedSelection (a.toStrongHom.sourceSelectionForTarget PA) := by
    rintro i j hij ⟨k, hk, hkj⟩
    exact ⟨k, hk, (image_mono hij).trans hkj⟩
  apply (hSA.and hSB hdSA).trans
  rintro _ ⟨i, rfl⟩ x hx
  obtain ⟨⟨α, hα, ha⟩, ⟨β, hβ, hb⟩⟩ := i.property
  obtain ⟨U, hU, hUT, hαU⟩ := hα
  obtain ⟨V, hV, hVT, hβV⟩ := hβ
  obtain ⟨k, hk⟩ := f.target_exists α
  obtain ⟨l, hl⟩ := g.target_exists β
  let h := a.comp f
  have hIk : h.baseMap '' range (T.atlas.chart i.val) ⊆ range (C.atlas.chart k) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hk ⟨_, ha ⟨y, hy, rfl⟩, rfl⟩
  have hIl : h.baseMap '' range (T.atlas.chart i.val) ⊆ range (C.atlas.chart l) := by
    rintro _ ⟨y, hy, rfl⟩
    have he : h.baseMap y = (b.comp g).baseMap y := congrArg (fun q => q.baseMap y) hab
    exact he.symm ▸ hl ⟨_, hb ⟨y, hy, rfl⟩, rfl⟩
  have hL := (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp
    (C.atlas.isNet_chartFamily.2 _ ⟨k, rfl⟩ _ ⟨l, rfl⟩)
  obtain ⟨σ, hf, hs, hm, hn⟩ := hL _ (mem_singleton _) (h.baseMap x)
    ⟨hIk ⟨x, hx, rfl⟩, hIl ⟨x, hx, rfl⟩⟩
  let R : Set T.space := range (T.atlas.chart i.val)
  let δ : Set (Set T.space) := (fun F => R ∩ h.baseMap ⁻¹' F) '' σ
  have hδ : ⋃₀ δ = R ∩ h.baseMap ⁻¹' ⋃₀ σ := by
    ext y
    constructor
    · rintro ⟨_, ⟨F, hF, rfl⟩, hy⟩
      exact ⟨hy.1, F, hF, hy.2⟩
    · rintro ⟨hyR, F, hF, hyF⟩
      exact ⟨_, ⟨F, hF, rfl⟩, hyR, hyF⟩
  refine ⟨δ, hf.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨F, hF, rfl⟩
    obtain ⟨m, hmF⟩ := hs hF
    change range (C.atlas.chart m) = F at hmF
    have hmk : range (C.atlas.chart m) ⊆ range (C.atlas.chart k) :=
      (hmF ▸ (hm F hF).1).trans inter_subset_left
    have hml : range (C.atlas.chart m) ⊆ range (C.atlas.chart l) :=
      (hmF ▸ (hm F hF).1).trans inter_subset_right
    obtain ⟨c, hc⟩ := exists_chart_preimage (f := h) hT i.val hIk hmk
    obtain ⟨α', hα'⟩ := exists_chart_preimage (f := f) hA α hk hmk
    obtain ⟨β', hβ'⟩ := exists_chart_preimage (f := g) hB β hl hml
    let p : PairIndex f g := ⟨(α', β'), m, ⟨by
      rintro _ ⟨y, hy, rfl⟩
      rw [hα'] at hy
      exact hy.2, by
      rintro _ ⟨y, hy, rfl⟩
      rw [hβ'] at hy
      exact hy.2⟩⟩
    have hp : p ∈ goodPairs f g :=
      ⟨U, V, hU, hV, hUT, hVT,
        hα'.symm ▸ inter_subset_left.trans hαU,
        hβ'.symm ▸ inter_subset_left.trans hβV⟩
    have hca : a.baseMap '' range (T.atlas.chart c) ⊆ range (A.atlas.chart p.val.1) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hc] at hy
      change a.baseMap y ∈ range (A.atlas.chart α')
      rw [hα']
      exact ⟨ha ⟨y, hy.1, rfl⟩, hy.2⟩
    have hcb : b.baseMap '' range (T.atlas.chart c) ⊆ range (B.atlas.chart p.val.2) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [hc] at hy
      change b.baseMap y ∈ range (B.atlas.chart β')
      rw [hβ']
      have he : h.baseMap y = (b.comp g).baseMap y := congrArg (fun q => q.baseMap y) hab
      refine ⟨hb ⟨y, hy.1, rfl⟩, ?_⟩
      change (b.comp g).baseMap y ∈ range (C.atlas.chart m)
      exact he ▸ hy.2
    refine ⟨⟨c, p, hp, hca, hcb⟩, ?_⟩
    exact hc.trans (by rw [hmF])
  · rintro _ ⟨F, hF, rfl⟩
    exact ⟨inter_subset_left, hx, (hm F hF).2⟩
  · rw [hδ]
    have ht : Tendsto h.baseMap (𝓝[R] x)
        (𝓝[range (C.atlas.chart k) ∩ range (C.atlas.chart l)] (h.baseMap x)) :=
      h.baseMap.continuous.continuousWithinAt.tendsto_nhdsWithin
        (fun y hy => ⟨hIk ⟨y, hy, rfl⟩, hIl ⟨y, hy, rfl⟩⟩)
    exact Filter.inter_mem self_mem_nhdsWithin (ht hn)

/-- The actual downward-closed source refinement with good pair-chart
witnesses for every selected original chart. -/
def alignedSourceSelection
    (hT : T.atlas.HasAllLocalDomains) (hA : A.atlas.HasAllLocalDomains)
    (hB : B.atlas.HasAllLocalDomains) (hab : a.comp f = b.comp g) : T.atlas.RefiningSelection where
  carrier := alignedSourceCharts f g a b
  downward_closed := alignedSourceCharts_downward f g a b
  locally_refining := alignedSourceCharts_locallyRefining f g a b hT hA hB hab

end FibreProduct

end Langlands.Analytic
