import Langlands.Geometry.Analytic.FibreProductPatchHausdorff

/-! # Locally Hausdorff gluing and embedded local pair charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.FibreProduct

open Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)

private theorem t2Space_subset {X : Type*} [TopologicalSpace X]
    {S T : Set X} [T2Space T] (hST : S ⊆ T) : T2Space S :=
  (IsEmbedding.subtypeVal.codRestrict T (fun x : S => hST x.property)).t2Space

/-- Local Hausdorffness of an atlas supplies an open Hausdorff neighborhood. -/
theorem exists_open_hausdorff_neighborhood {X : Type*} [TopologicalSpace X]
    (a : IndexedAffinoidAtlas.{u, _, w} K X) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ T2Space U := by
  obtain ⟨H, hH, hHT⟩ := a.locallyHausdorff x
  let : T2Space H := hHT
  exact ⟨interior H, isOpen_interior, mem_interior_iff_mem_nhds.mpr hH,
    t2Space_subset interior_subset⟩

/-- Pair charts whose factor chart ranges lie in open Hausdorff patches. -/
def goodPairs : Set (PairIndex f g) :=
  {p | ∃ (U : Set A.space) (V : Set B.space), IsOpen U ∧ IsOpen V ∧
    T2Space U ∧ T2Space V ∧ p ∈ patchPairs f g U V}

theorem isDownwardClosed_goodPairs : (chartSystem f g).IsDownwardClosed (goodPairs f g) := by
  rintro p q hpq ⟨U, V, hU, hV, hUT, hVT, hq⟩
  exact ⟨U, V, hU, hV, hUT, hVT, isDownwardClosed_patchPairs f g U V hpq hq⟩

/-- Every original spectrum point has an actual good subpair restriction
image as a neighborhood. This is a statement in spectrum coordinates. -/
theorem exists_goodPair_neighborhood
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (p : PairIndex f g) (t : BanachSpectrum (algebra f g p)) :
    ∃ (q : PairIndex f g) (hqp : Sub f g q p), q ∈ goodPairs f g ∧
      range ((chartSystem f g).pull hqp) ∈ 𝓝 t := by
  obtain ⟨U, hU, htU, hUT⟩ := exists_open_hausdorff_neighborhood
    A.atlas (A.atlas.chart p.val.1 (leftPoint f g p t))
  obtain ⟨V, hV, htV, hVT⟩ := exists_open_hausdorff_neighborhood
    B.atlas (B.atlas.chart p.val.2 (rightPoint f g p t))
  obtain ⟨q, hqp, hq, hqt⟩ := exists_patchPair_neighborhood f g hA hB hU hV p t htU htV
  exact ⟨q, hqp, ⟨U, V, hU, hV, hUT, hVT, hq⟩, hqt⟩

/-- Good charts are embedded in the unrestricted quotient, by passing
through the actual open factor-patch quotient. -/
theorem isEmbedding_goodChart
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    {p : PairIndex f g} (hp : p ∈ goodPairs f g) :
    IsEmbedding ((chartSystem f g).chart p) := by
  obtain ⟨U, V, hU, hV, hUT, hVT, hp⟩ := hp
  let : T2Space U := hUT
  let : T2Space V := hVT
  exact (isOpenEmbedding_patchSubsystem f g hA hB hU hV).isEmbedding.comp
    (isClosedEmbedding_patchChart f g U V ⟨p, hp⟩).isEmbedding

/-- The good pair-chart support is the entire unrestricted quotient. -/
theorem subsystemSupport_goodPairs
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains) :
    (chartSystem f g).subsystemSupport (goodPairs f g) = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨p, t, rfl⟩ := (chartSystem f g).exists_chart z
  obtain ⟨q, hqp, hq, hqt⟩ := exists_goodPair_neighborhood f g hA hB p t
  obtain ⟨s, hs⟩ := mem_of_mem_nhds hqt
  exact ⟨⟨q, hq⟩, s, ((chartSystem f g).chart_pull hqp s).symm.trans
    (congrArg ((chartSystem f g).chart p) hs)⟩

/-- Every quotient point has open Hausdorff factor patches over a common
open Hausdorff base patch. -/
theorem exists_hausdorff_patches (z : (chartSystem f g).Space) :
    ∃ (U : Set A.space) (V : Set B.space) (W : Set C.space),
      IsOpen U ∧ IsOpen V ∧ IsOpen W ∧ T2Space U ∧ T2Space V ∧ T2Space W ∧
      fst f g z ∈ U ∧ snd f g z ∈ V ∧ f.baseMap '' U ⊆ W ∧ g.baseMap '' V ⊆ W := by
  obtain ⟨U₀, hU₀, hzU₀, hUT⟩ := exists_open_hausdorff_neighborhood A.atlas (fst f g z)
  obtain ⟨V₀, hV₀, hzV₀, hVT⟩ := exists_open_hausdorff_neighborhood B.atlas (snd f g z)
  obtain ⟨W, hW, hzW, hWT⟩ :=
    exists_open_hausdorff_neighborhood C.atlas (f.baseMap (fst f g z))
  let : T2Space U₀ := hUT
  let : T2Space V₀ := hVT
  refine ⟨U₀ ∩ f.baseMap ⁻¹' W, V₀ ∩ g.baseMap ⁻¹' W, W,
    hU₀.inter (hW.preimage f.baseMap.continuous), hV₀.inter (hW.preimage g.baseMap.continuous),
    hW, t2Space_subset inter_subset_left, t2Space_subset inter_subset_left, hWT,
    ⟨hzU₀, hzW⟩, ⟨hzV₀, ?_⟩, ?_, ?_⟩
  · change g.baseMap (snd f g z) ∈ W
    rwa [← baseMap_fst f g z]
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2

/-- With domain-saturated factor and base atlases, the unrestricted pair
quotient is locally Hausdorff, without global separation assumptions. -/
theorem locallyHausdorff_chartSystem
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) (z : (chartSystem f g).Space) :
    ∃ N : Set (chartSystem f g).Space, N ∈ 𝓝 z ∧ T2Space N := by
  obtain ⟨U, V, W, hU, hV, hW, hUT, hVT, hWT, hzU, hzV, hUW, hVW⟩ :=
    exists_hausdorff_patches f g z
  let : T2Space U := hUT
  let : T2Space V := hVT
  let : T2Space W := hWT
  let : T2Space (patchSystem f g U V).Space :=
    t2Space_patchSystem f g hU hV hA hB hC hW hUW hVW
  have he : IsOpenEmbedding (patchMap f g U V) :=
    isOpenEmbedding_patchSubsystem f g hA hB hU hV
  have hz : z ∈ range (patchMap f g U V) := by
    change z ∈ range ((chartSystem f g).subsystemMap (patchPairs f g U V)
      (isDownwardClosed_patchPairs f g U V))
    rw [(chartSystem f g).range_subsystemMap,
      subsystemSupport_patchPairs f g hA hB hU hV]
    exact ⟨hzU, hzV⟩
  exact ⟨range (patchMap f g U V), he.isOpen_range.mem_nhds hz,
    he.isEmbedding.toHomeomorph.t2Space⟩

/-- The nonempty good pair-chart ranges in the full quotient. -/
def goodChartFamily : Set (Set (chartSystem f g).Space) :=
  {T | T.Nonempty ∧ ∃ p ∈ goodPairs f g, range ((chartSystem f g).chart p) = T}

end Langlands.Analytic.FibreProduct
