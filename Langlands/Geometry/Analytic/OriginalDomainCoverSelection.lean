import Langlands.Geometry.Analytic.CommonSubatlas
import Langlands.Geometry.Analytic.OriginalChartDomains
import Langlands.Geometry.Analytic.AtlasTopology.NestedRestriction

/-! # Refining selections assembled over original-domain covers -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

open Set Filter
open scoped Topology

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

/-- A downward-closed selection that is a quasinet refines every original
chart, by the original net's intersection axiom. -/
theorem IsDownwardClosedSelection.isLocallyRefining_of_isQuasinet
    {P : a.Index → Prop} (hd : a.IsDownwardClosedSelection P)
    (hq : AtlasTopology.IsQuasinet (a.selectedChartFamily P)) :
    a.IsLocallyRefiningSelection P := by
  have hglob : AtlasTopology.LocallyRefines (a.selectedChartFamily P) {Set.univ} := by
    intro U hU x _
    obtain rfl := mem_singleton_iff.mp hU
    obtain ⟨σ, hf, hs, hm, hn⟩ := hq x
    exact ⟨σ, hf, hs, fun V hV => ⟨subset_univ _, hm V hV⟩,
      by simpa only [nhdsWithin_univ] using hn⟩
  have hi := hglob.intersectionFamily
    (AtlasTopology.LocallyRefines.refl (Set.range (fun i => Set.range (a.chart i))))
  have ht : AtlasTopology.intersectionFamily {Set.univ}
      (Set.range (fun i => Set.range (a.chart i))) =
      Set.range (fun i => Set.range (a.chart i)) := by
    ext W
    constructor
    · rintro ⟨U, hU, V, hV, rfl⟩
      obtain rfl := mem_singleton_iff.mp hU
      simpa only [univ_inter] using hV
    · intro hW
      exact ⟨Set.univ, mem_singleton _, W, hW, (univ_inter W).symm⟩
  rw [ht] at hi
  apply hi.trans
  rintro W ⟨U, ⟨i, rfl⟩, V, ⟨j, rfl⟩, rfl⟩ x hx
  obtain ⟨σ, hf, hs, hm, hn⟩ :=
    a.isNet_chartFamily.locallyRefines_intersectionFamily _
      ⟨_, ⟨i.val, rfl⟩, _, ⟨j, rfl⟩, rfl⟩ x hx
  refine ⟨σ, hf, ?_, hm, hn⟩
  intro V hV
  obtain ⟨t, ht⟩ := hs hV
  change Set.range (a.chart t) = V at ht
  refine ⟨⟨t, hd t i.val ?_ i.property⟩, ht⟩
  rw [ht]
  exact ((hm V hV).1).trans inter_subset_left

variable {ι : Type z} (D : ι → a.OriginalChartDomain)
  (R : ∀ k, (a.subspaceAtlas (D k).carrier (D k).is_domain).RefiningSelection)

/-- Select an original chart when its copy in some covering domain is selected
there. Both the domain and the literal original index are retained. -/
def domainCoverSelectionPredicate (i : a.Index) : Prop :=
  ∃ (k : ι) (hi : Set.range (a.chart i) ⊆ (D k).carrier),
    (⟨i, hi⟩ : a.SubspaceChart (D k).carrier) ∈ R k

theorem domainCoverSelectionPredicate_downwardClosed :
    a.IsDownwardClosedSelection (domainCoverSelectionPredicate D R) := by
  rintro i j hij ⟨k, hj, hR⟩
  refine ⟨k, hij.trans hj, ?_⟩
  exact (R k).downward_closed ⟨i, hij.trans hj⟩ ⟨j, hj⟩
    (a.subspaceChart_subset (D k).carrier _ _ hij) hR

/-- Each local selection supplies finite relative neighborhoods of its domain
by the ambient images of its selected original charts. -/
theorem domainCoverSelectionPredicate_locallyRefines :
    AtlasTopology.LocallyRefines (a.selectedChartFamily (domainCoverSelectionPredicate D R))
      (Set.range (fun k => (D k).carrier)) := by
  rintro U ⟨k, rfl⟩ x hx
  let b := a.subspaceAtlas (D k).carrier (D k).is_domain
  have hq : AtlasTopology.IsQuasinet (b.selectedChartFamily (R k).carrier) :=
    (b.isNet_selectedChartFamily (R k).carrier (R k).locally_refining).1
  have hr : AtlasTopology.LocallyRefines
      ((fun V : Set (D k).carrier => Subtype.val '' V) '' b.selectedChartFamily (R k).carrier)
      {(D k).carrier} := by
    apply (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp
    rwa [AtlasTopology.restrictedFamily_subtype_images]
  have hs : ((fun V : Set (D k).carrier => Subtype.val '' V) ''
      b.selectedChartFamily (R k).carrier) ⊆
      a.selectedChartFamily (domainCoverSelectionPredicate D R) := by
    rintro V ⟨W, ⟨c, rfl⟩, rfl⟩
    have heq : Subtype.val '' Set.range (b.chart c.val) =
        Set.range (a.chart c.val.val) := by
      ext y
      constructor
      · rintro ⟨s, ⟨t, rfl⟩, rfl⟩
        exact ⟨t, rfl⟩
      · rintro ⟨t, rfl⟩
        exact ⟨b.chart c.val t, ⟨t, rfl⟩, rfl⟩
    exact ⟨⟨c.val.val, k, c.val.property, c.property⟩, heq.symm⟩
  exact (hr.mono hs Subset.rfl) _ (mem_singleton _) x hx

/-- Local selections over a quasinet domain cover form a global quasinet. -/
theorem domainCoverSelectionPredicate_isQuasinet
    (hD : AtlasTopology.LocallyRefines (Set.range (fun k => (D k).carrier)) {Set.univ}) :
    AtlasTopology.IsQuasinet (a.selectedChartFamily (domainCoverSelectionPredicate D R)) := by
  have h := hD.trans (domainCoverSelectionPredicate_locallyRefines D R)
  intro x
  obtain ⟨σ, hf, hs, hm, hn⟩ := h Set.univ (mem_singleton _) x (mem_univ x)
  exact ⟨σ, hf, hs, fun V hV => (hm V hV).2,
    by simpa only [nhdsWithin_univ] using hn⟩

/-- Construct a global refining selection from selections on actual covering
domains. No output global selection or refined atlas is assumed. -/
def coverRefiningSelection
    (hD : AtlasTopology.LocallyRefines (Set.range (fun k => (D k).carrier)) {Set.univ}) :
    a.RefiningSelection where
  carrier := domainCoverSelectionPredicate D R
  downward_closed := domainCoverSelectionPredicate_downwardClosed D R
  locally_refining := IsDownwardClosedSelection.isLocallyRefining_of_isQuasinet
    (domainCoverSelectionPredicate_downwardClosed D R)
    (domainCoverSelectionPredicate_isQuasinet D R hD)

@[simp]
theorem mem_coverRefiningSelection
    (hD : AtlasTopology.LocallyRefines (Set.range (fun k => (D k).carrier)) {Set.univ})
    (i : a.Index) :
    i ∈ coverRefiningSelection D R hD ↔
      ∃ (k : ι) (hi : Set.range (a.chart i) ⊆ (D k).carrier),
        (⟨i, hi⟩ : a.SubspaceChart (D k).carrier) ∈ R k := Iff.rfl

theorem coverRefiningSelection_mono
    (R' : ∀ k, (a.subspaceAtlas (D k).carrier (D k).is_domain).RefiningSelection)
    (hD : AtlasTopology.LocallyRefines (Set.range (fun k => (D k).carrier)) {Set.univ})
    (hR : ∀ k, R k ≤ R' k) :
    coverRefiningSelection D R hD ≤ coverRefiningSelection D R' hD := by
  rintro i ⟨k, hi, h⟩
  exact ⟨k, hi, hR k h⟩

end IndexedAffinoidAtlas

end Langlands.Analytic
