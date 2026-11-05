import Langlands.Geometry.Analytic.StrongLocalDomainInverseImageNaturality
import Langlands.Geometry.Analytic.SaturatedChartCoverRefinement

/-! # Actual source refinements subordinate to a target subatlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K} (f : StrongHom A B)

/-- Source charts whose complete image lies in a selected target chart. -/
def sourceSelectionForTarget (P : B.atlas.Index → Prop) (i : A.atlas.Index) : Prop :=
  ∃ j, P j ∧ f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)

/-- Pulling back an actual original relative chart has exactly the expected
ambient inverse-image locus. -/
theorem localDomainInverseImage_originalChart_locus (U : LocalDomain A.atlas)
    (j : B.atlas.Index)
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j))
    (k : B.atlas.Index)
    (hk : Set.range (B.atlas.chart k) ⊆ Set.range (B.atlas.chart j)) :
    (f.localDomainInverseImage U j h (B.atlas.restrictionDomain k j hk)).locus =
      U.locus ∩ f.baseMap ⁻¹' Set.range (B.atlas.chart k) := by
  rw [f.localDomainInverseImage_locus]
  change U.locus ∩ f.baseMap ⁻¹'
      (B.atlas.chart j '' (B.atlas.chart j ⁻¹' Set.range (B.atlas.chart k))) = _
  rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left.mpr hk]

/-- Choose an original source chart representing the actual full pushout
domain. The closure premise is proved for the constructed saturated atlas. -/
def inverseImageOriginalChart (ha : A.atlas.HasAllLocalDomains)
    (U : LocalDomain A.atlas) (j : B.atlas.Index)
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j))
    (k : B.atlas.Index)
    (hk : Set.range (B.atlas.chart k) ⊆ Set.range (B.atlas.chart j)) :
    A.atlas.Index :=
  ha.domainChartIndex U.index
    (f.localDomainInverseImage U j h (B.atlas.restrictionDomain k j hk)).domain

theorem range_inverseImageOriginalChart (ha : A.atlas.HasAllLocalDomains)
    (U : LocalDomain A.atlas) (j : B.atlas.Index)
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j))
    (k : B.atlas.Index)
    (hk : Set.range (B.atlas.chart k) ⊆ Set.range (B.atlas.chart j)) :
    Set.range (A.atlas.chart (f.inverseImageOriginalChart ha U j h k hk)) =
      U.locus ∩ f.baseMap ⁻¹' Set.range (B.atlas.chart k) :=
  (ha.range_domainChartIndex U.index _).trans
    (f.localDomainInverseImage_originalChart_locus U j h k hk)

/-- The source-chart replacement retains actual bounded inverse maps over
the source parent algebra, constructed by the full universal properties. -/
def inverseImageOriginalChartDomainIso (ha : A.atlas.HasAllLocalDomains)
    (U : LocalDomain A.atlas) (j : B.atlas.Index)
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j))
    (k : B.atlas.Index)
    (hk : Set.range (B.atlas.chart k) ⊆ Set.range (B.atlas.chart j)) :
    (f.localDomainInverseImage U j h (B.atlas.restrictionDomain k j hk)).domain ≅
      ha.chartDomain U.index
        (f.localDomainInverseImage U j h (B.atlas.restrictionDomain k j hk)).domain :=
  ha.chartDomainIso U.index _

theorem inverseImageOriginalChart_selected (ha : A.atlas.HasAllLocalDomains)
    (P : B.atlas.Index → Prop) (U : LocalDomain A.atlas) (j : B.atlas.Index)
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j))
    (k : B.atlas.Index) (hPk : P k)
    (hk : Set.range (B.atlas.chart k) ⊆ Set.range (B.atlas.chart j)) :
    f.sourceSelectionForTarget P (f.inverseImageOriginalChart ha U j h k hk) := by
  refine ⟨k, hPk, ?_⟩
  rw [f.range_inverseImageOriginalChart]
  rintro _ ⟨x, hx, rfl⟩
  exact hx.2

/-- Relative finite target neighborhoods pull back to a relative finite
neighborhood made of actual source chart domains. No chart intersection is
assumed compact, and no global finite target cover is used. -/
theorem sourceSelectionForTarget_locallyRefining
    (ha : A.atlas.HasAllLocalDomains) (P : B.atlas.Index → Prop)
    (hP : B.atlas.IsLocallyRefiningSelection P) :
    A.atlas.IsLocallyRefiningSelection (f.sourceSelectionForTarget P) := by
  classical
  rintro _ ⟨i, rfl⟩ x hx
  obtain ⟨j, hj⟩ := f.target_exists i
  obtain ⟨σ, hf, hs, hxσ, hn⟩ :=
    hP (Set.range (B.atlas.chart j)) ⟨j, rfl⟩ (f.baseMap x) (hj ⟨x, hx, rfl⟩)
  let T : Set A.space := Set.range (A.atlas.chart i)
  let δ : Set (Set A.space) := (fun V => T ∩ f.baseMap ⁻¹' V) '' σ
  have hδ : ⋃₀ δ = T ∩ f.baseMap ⁻¹' ⋃₀ σ := by
    ext y
    constructor
    · rintro ⟨_, ⟨V, hV, rfl⟩, hy⟩
      exact ⟨hy.1, V, hV, hy.2⟩
    · rintro ⟨hyT, V, hV, hyV⟩
      exact ⟨_, ⟨V, hV, rfl⟩, hyT, hyV⟩
  refine ⟨δ, hf.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    obtain ⟨k, hk⟩ := hs hV
    change Set.range (B.atlas.chart k.val) = V at hk
    have hkj : Set.range (B.atlas.chart k.val) ⊆ Set.range (B.atlas.chart j) := by
      rw [hk]
      exact (hxσ V hV).1
    let U : LocalDomain A.atlas := ⟨i, Domain.whole K (A.atlas.algebra i)⟩
    have hU : U.locus = T := Set.image_univ
    have hlocal : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j) := hU ▸ hj
    refine ⟨⟨f.inverseImageOriginalChart ha U j hlocal k.val hkj,
      f.inverseImageOriginalChart_selected ha P U j hlocal k.val k.property hkj⟩, ?_⟩
    exact (f.range_inverseImageOriginalChart ha U j hlocal k.val hkj).trans
      (by rw [hU, hk])
  · rintro _ ⟨V, hV, rfl⟩
    exact ⟨Set.inter_subset_left, hx, (hxσ V hV).2⟩
  · rw [hδ]
    have hc : Tendsto f.baseMap (𝓝[T] x) (𝓝[Set.range (B.atlas.chart j)] (f.baseMap x)) :=
      f.baseMap.continuous.continuousWithinAt.tendsto_nhdsWithin
        (fun _ hy => hj ⟨_, hy, rfl⟩)
    exact Filter.inter_mem self_mem_nhdsWithin (hc hn)

/-- Construct the actual same-space source refinement subordinate to the
selected target chart family. -/
def targetSubatlasSource (ha : A.atlas.HasAllLocalDomains)
    (P : B.atlas.Index → Prop) (hP : B.atlas.IsLocallyRefiningSelection P) :
    AffinoidAtlasPresentation.{u, v, w} K :=
  A.subpresentation (f.sourceSelectionForTarget P)
    (f.sourceSelectionForTarget_locallyRefining ha P hP)

/-- Every admissible bounded pullback remains the original pullback of f;
the newly proved local refinement supplies the missing source atlas. -/
def targetSubatlasLift (ha : A.atlas.HasAllLocalDomains)
    (P : B.atlas.Index → Prop) (hP : B.atlas.IsLocallyRefiningSelection P) :
    StrongHom (f.targetSubatlasSource ha P hP) (B.subpresentation P hP) where
  baseMap := f.baseMap
  target_exists i := by
    obtain ⟨j, hj, h⟩ := i.property
    exact ⟨⟨j, hj⟩, h⟩
  pullback i j h := f.pullback i.val j.val h
  chart_comm i j h x := f.chart_comm i.val j.val h x
  restriction_comm i i' j j' hi hj h h' :=
    f.restriction_comm i.val i'.val j.val j'.val hi hj h h'

@[simp]
theorem targetSubatlasLift_baseMap (ha : A.atlas.HasAllLocalDomains)
    (P : B.atlas.Index → Prop) (hP : B.atlas.IsLocallyRefiningSelection P) :
    (f.targetSubatlasLift ha P hP).baseMap = f.baseMap := rfl

@[simp]
theorem targetSubatlasLift_pullback (ha : A.atlas.HasAllLocalDomains)
    (P : B.atlas.Index → Prop) (hP : B.atlas.IsLocallyRefiningSelection P)
    (i : (f.targetSubatlasSource ha P hP).atlas.Index)
    (j : (B.subpresentation P hP).atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i.val) ⊆
      Set.range (B.atlas.chart j.val)) :
    (f.targetSubatlasLift ha P hP).pullback i j h = f.pullback i.val j.val h := rfl

/-- The refinement map is a full quasi-isomorphism with the literal identity
on the source space and every original bounded restriction. -/
def targetSubatlasSourceInclusion (ha : A.atlas.HasAllLocalDomains)
    (P : B.atlas.Index → Prop) (hP : B.atlas.IsLocallyRefiningSelection P) :
    StrongHom (f.targetSubatlasSource ha P hP) A :=
  A.strongSubatlasInclusion (f.sourceSelectionForTarget P)
    (f.sourceSelectionForTarget_locallyRefining ha P hP)

theorem isQuasiIso_targetSubatlasSourceInclusion (ha : A.atlas.HasAllLocalDomains)
    (P : B.atlas.Index → Prop) (hP : B.atlas.IsLocallyRefiningSelection P) :
    (f.targetSubatlasSourceInclusion ha P hP).IsQuasiIso :=
  A.isQuasiIso_strongSubatlasInclusion (f.sourceSelectionForTarget P)
    (f.sourceSelectionForTarget_locallyRefining ha P hP)

/-- A quasi-isomorphism remains one after the constructed source refinement
and target selection, with its full local representations unchanged. -/
theorem IsQuasiIso.targetSubatlasLift {f : StrongHom A B} (hf : f.IsQuasiIso)
    (ha : A.atlas.HasAllLocalDomains) (P : B.atlas.Index → Prop)
    (hP : B.atlas.IsLocallyRefiningSelection P) :
    (f.targetSubatlasLift ha P hP).IsQuasiIso :=
  ⟨hf.1, fun i j h => hf.2 i.val j.val h⟩

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
