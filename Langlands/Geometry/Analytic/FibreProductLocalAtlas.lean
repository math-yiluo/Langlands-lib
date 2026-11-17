import Langlands.Geometry.Analytic.FibreProductLocalCharts
import Langlands.Geometry.Analytic.AtlasTopology.NestedRestriction

/-! # The local affinoid atlas of the unrestricted fibre-product gluing -/

noncomputable section

universe u v w

namespace Langlands.Analytic.FibreProduct

open Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)

private theorem subspace_originalChart_domain {X : Type*} [TopologicalSpace X]
    (a : IndexedAffinoidAtlas.{u, _, w} K X) (ha : a.HasAllLocalDomains)
    {U : Set X} (hU : IsOpen U) (i : a.Index) :
    AtlasTopology.IsQuasinet (AtlasTopology.restrictedFamily
      (range fun c => range (a.subspaceChart U c)) (Subtype.val ⁻¹' range (a.chart i))) := by
  rw [a.subspaceChartFamily_eq, AtlasTopology.isQuasinet_restrictedFamily_subtype_iff,
    Subtype.image_preimage_val]
  exact a.isNet_chartFamily.isQuasinet_restrictedFamily_inter
    (ha.isOriginalChartDomain_of_isOpen hU) (a.isOriginalChartDomain_chart i)

/-- Good chart ranges belong to the preimage-intersection family of the
original factor atlas nets. -/
theorem goodChartFamily_subset :
    goodChartFamily f g ⊆ AtlasTopology.preimageProductFamily (fst f g) (snd f g)
      (range fun a => range (A.atlas.chart a)) (range fun b => range (B.atlas.chart b)) := by
  rintro _ ⟨hne, p, -, rfl⟩
  exact ⟨hne, _, ⟨p.val.1, rfl⟩, _, ⟨p.val.2, rfl⟩, range_chart f g p⟩

/-- Local Hausdorff patch nets refine the original factor-chart preimages.
The finite relative neighborhoods are transported through an open embedding. -/
theorem locallyRefines_goodChartFamily
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) :
    AtlasTopology.LocallyRefines (goodChartFamily f g)
      (AtlasTopology.preimageProductFamily (fst f g) (snd f g)
        (range fun a => range (A.atlas.chart a)) (range fun b => range (B.atlas.chart b))) := by
  classical
  rintro _ ⟨-, _, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ z hz
  obtain ⟨U, V, W, hU, hV, hW, hUT, hVT, hWT, hzU, hzV, hUW, hVW⟩ :=
    exists_hausdorff_patches f g z
  let : T2Space U := hUT
  let : T2Space V := hVT
  let : T2Space W := hWT
  let P := patchSystem f g U V
  let e := patchMap f g U V
  have he : IsOpenEmbedding e := isOpenEmbedding_patchSubsystem f g hA hB hU hV
  have hzrange : z ∈ range e := by
    change z ∈ range ((chartSystem f g).subsystemMap (patchPairs f g U V)
      (isDownwardClosed_patchPairs f g U V))
    rw [(chartSystem f g).range_subsystemMap,
      subsystemSupport_patchPairs f g hA hB hU hV]
    exact ⟨hzU, hzV⟩
  obtain ⟨z', rfl⟩ := hzrange
  have hLA := (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp
    (subspace_originalChart_domain A.atlas hA hU a)
  have hLB := (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp
    (subspace_originalChart_domain B.atlas hB hV b)
  have hLP := AtlasTopology.locallyRefines_preimageProductFamily
    (continuous_patchFst f g U V) (continuous_patchSnd f g U V) hLA hLB
  have hL := hLP.trans (locallyRefines_patchChartFamily f g U V hA hB hC hW hUW hVW)
  obtain ⟨σ, hf, hs, hm, hn⟩ := hL _ (mem_singleton _) z' hz
  let δ : Set (Set (chartSystem f g).Space) := (fun T : Set P.Space => e '' T) '' σ
  refine ⟨δ, hf.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨T, hT, rfl⟩
    obtain ⟨hne, p, rfl⟩ := hs hT
    refine ⟨hne.image e, p.val, ⟨U, V, hU, hV, hUT, hVT, p.property⟩, ?_⟩
    ext y
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨P.chart p t, ⟨t, rfl⟩, ht⟩
    · rintro ⟨_, ⟨t, rfl⟩, ht⟩
      exact ⟨t, ht⟩
  · rintro _ ⟨T, hT, rfl⟩
    refine ⟨?_, ⟨z', (hm T hT).2, rfl⟩⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (hm T hT).1 hx
  · obtain ⟨O, hO, hzO, hOsub⟩ := mem_nhdsWithin.mp hn
    apply mem_nhdsWithin.mpr
    refine ⟨e '' O, he.isOpenMap O hO, ⟨z', hzO, rfl⟩, ?_⟩
    rintro _ ⟨⟨x, hxO, rfl⟩, hxM⟩
    obtain ⟨T, hT, hxT⟩ := hOsub ⟨hxO, hxM⟩
    exact ⟨e '' T, ⟨T, hT, rfl⟩, ⟨x, hxT, rfl⟩⟩

/-- The unrestricted quotient has the net of nonempty embedded good charts. -/
theorem isNet_goodChartFamily
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) : AtlasTopology.IsNet (goodChartFamily f g) :=
  (AtlasTopology.IsNet.preimageProductFamily (continuous_fst f g) (continuous_snd f g)
    A.atlas.isNet_chartFamily B.atlas.isNet_chartFamily).of_locallyRefines
      (goodChartFamily_subset f g) (locallyRefines_goodChartFamily f g hA hB hC)

/-- Distinct nonempty good chart domains index the local atlas. -/
def LocalAtlasIndex : Type (max u w) :=
  {T : Set (chartSystem f g).Space // T ∈ goodChartFamily f g}

variable {f g} in
/-- A representative original pair for an actual good chart domain. -/
def LocalAtlasIndex.rep (T : LocalAtlasIndex f g) : PairIndex f g := T.property.2.choose

variable {f g} in
theorem LocalAtlasIndex.good_rep (T : LocalAtlasIndex f g) : T.rep ∈ goodPairs f g :=
  T.property.2.choose_spec.1

variable {f g} in
theorem LocalAtlasIndex.range_rep (T : LocalAtlasIndex f g) :
    range ((chartSystem f g).chart T.rep) = T.val := T.property.2.choose_spec.2

theorem range_localRep_eq_goodChartFamily :
    range (fun T : LocalAtlasIndex f g => range ((chartSystem f g).chart T.rep)) =
      goodChartFamily f g := by
  ext S
  constructor
  · rintro ⟨T, rfl⟩
    change range ((chartSystem f g).chart T.rep) ∈ goodChartFamily f g
    rw [T.range_rep]
    exact T.property
  · intro hS
    exact ⟨⟨S, hS⟩, LocalAtlasIndex.range_rep ⟨S, hS⟩⟩

/-- The actual affinoid atlas of the unrestricted gluing, with no global
Hausdorff assumptions. Its space and index universe is still `max u w`. -/
def localAtlas
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) :
    IndexedAffinoidAtlas.{u, max u w, max u w} K (chartSystem f g).Space where
  Index := LocalAtlasIndex f g
  algebra T := algebra f g T.rep
  chart T := (chartSystem f g).chart T.rep
  isEmbedding_chart T := isEmbedding_goodChart f g hA hB T.good_rep
  chartDomain_injective T T' h :=
    Subtype.ext (T.range_rep.symm.trans (h.trans T'.range_rep))
  locallyHausdorff := locallyHausdorff_chartSystem f g hA hB hC
  isNet_chartFamily := by
    rw [range_localRep_eq_goodChartFamily]
    exact isNet_goodChartFamily f g hA hB hC
  restriction _ _ h := rangeRestriction f g h
  restriction_chart _ _ h x := chart_rangeRestriction f g h x
  restriction_universal _ _ h R φ hφ := rangeRestriction_universal f g h R φ hφ
  restriction_id T _ := rangeRestriction_self f g T.rep
  restriction_comp _ _ _ h₁ h₂ _ := rangeRestriction_comp f g h₁ h₂

/-- The locally Hausdorff affinoid atlas presentation of the actual gluing. -/
def localPresentation
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) : AffinoidAtlasPresentation.{u, max u w, max u w} K where
  space := TopCat.of (chartSystem f g).Space
  atlas := localAtlas f g hA hB hC

end Langlands.Analytic.FibreProduct
