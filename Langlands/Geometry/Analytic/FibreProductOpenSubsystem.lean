import Langlands.Geometry.Analytic.AffinoidChartSubsystem
import Langlands.Geometry.Analytic.FibreProductChartSystem
import Langlands.Geometry.Analytic.SaturatedAtlasDomainClosure
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalLaurentNeighborhoods

/-! # Open factor patches in a fibre-product chart gluing -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- In an atlas containing all local domains, every neighborhood in an
original spectrum contains the preimage of a smaller original chart
which is still a neighborhood of the spectrum point. -/
theorem exists_subchart_neighborhood (ha : a.HasAllLocalDomains)
    (i : a.Index) (x : BanachSpectrum (a.algebra i))
    (V : Set (BanachSpectrum (a.algebra i))) (hV : V ∈ 𝓝 x) :
    ∃ j : a.Index, range (a.chart j) ⊆ range (a.chart i) ∧
      a.chart i ⁻¹' range (a.chart j) ∈ 𝓝 x ∧
      a.chart i ⁻¹' range (a.chart j) ⊆ V := by
  obtain ⟨d, hd, hdV⟩ := RationalChart.exists_rational_neighborhood x V hV
  obtain ⟨j, hj⟩ := ha.exists_chart ⟨i, d.toDomain⟩
  have hj' : range (a.chart j) = a.chart i '' d.locus := hj
  have heq : a.chart i ⁻¹' range (a.chart j) = d.locus := by
    rw [hj', preimage_image_eq _ (a.isEmbedding_chart i).injective]
  exact ⟨j, hj' ▸ image_subset_range _ _, heq ▸ hd, heq ▸ hdV⟩

end IndexedAffinoidAtlas

namespace FibreProduct

open AffinoidAtlasPresentation

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}
    (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)

/-- Pairs whose two original factor charts are contained in the prescribed
factor patches. -/
def patchPairs (U : Set A.space) (V : Set B.space) : Set (PairIndex f g) :=
  {p | range (A.atlas.chart p.val.1) ⊆ U ∧ range (B.atlas.chart p.val.2) ⊆ V}

theorem isDownwardClosed_patchPairs (U : Set A.space) (V : Set B.space) :
    (chartSystem f g).IsDownwardClosed (patchPairs f g U V) := by
  intro p q hpq hq
  exact ⟨hpq.1.trans hq.1, hpq.2.trans hq.2⟩

/-- Every point of an original pair spectrum above the two open patches
has a contained pair chart whose restriction image is a neighborhood. -/
theorem exists_patchPair_neighborhood
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    {U : Set A.space} {V : Set B.space} (hU : IsOpen U) (hV : IsOpen V)
    (p : PairIndex f g) (t : BanachSpectrum (algebra f g p))
    (htU : A.atlas.chart p.val.1 (leftPoint f g p t) ∈ U)
    (htV : B.atlas.chart p.val.2 (rightPoint f g p t) ∈ V) :
    ∃ (q : PairIndex f g) (hqp : Sub f g q p),
      q ∈ patchPairs f g U V ∧
      range ((chartSystem f g).pull hqp) ∈ 𝓝 t := by
  obtain ⟨i, hip, hiN, hiU⟩ :=
    A.atlas.exists_subchart_neighborhood hA p.val.1 (leftPoint f g p t)
      (A.atlas.chart p.val.1 ⁻¹' U)
      ((hU.preimage (A.atlas.isEmbedding_chart p.val.1).continuous).mem_nhds htU)
  obtain ⟨j, hjp, hjN, hjV⟩ :=
    B.atlas.exists_subchart_neighborhood hB p.val.2 (rightPoint f g p t)
      (B.atlas.chart p.val.2 ⁻¹' V)
      ((hV.preimage (B.atlas.isEmbedding_chart p.val.2).continuous).mem_nhds htV)
  let q : PairIndex f g := ⟨(i, j), base f g p,
    ⟨(image_mono hip).trans (isCommonBase_base f g p).1,
      (image_mono hjp).trans (isCommonBase_base f g p).2⟩⟩
  have hqp : Sub f g q p := ⟨hip, hjp⟩
  refine ⟨q, hqp, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨s, rfl⟩ := hip hx
    exact hiU hx
  · intro x hx
    obtain ⟨s, rfl⟩ := hjp hx
    exact hjV hx
  · have hleft : leftPoint f g p ⁻¹'
        (A.atlas.chart p.val.1 ⁻¹' range (A.atlas.chart i)) ∈ 𝓝 t :=
      (BanachSpectrum.comapContinuous
        (leftMap f g p).toBoundedRingHom).continuous.continuousAt hiN
    have hright : rightPoint f g p ⁻¹'
        (B.atlas.chart p.val.2 ⁻¹' range (B.atlas.chart j)) ∈ 𝓝 t :=
      (BanachSpectrum.comapContinuous
        (rightMap f g p).toBoundedRingHom).continuous.continuousAt hjN
    apply Filter.mem_of_superset (Filter.inter_mem hleft hright)
    intro s hs
    exact (mem_range_restriction_iff f g q p hqp s).mpr hs

/-- The selected subsystem has precisely the inverse-image factor patch as
its support. No separation assumption is needed. -/
theorem subsystemSupport_patchPairs
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    {U : Set A.space} {V : Set B.space} (hU : IsOpen U) (hV : IsOpen V) :
    (chartSystem f g).subsystemSupport (patchPairs f g U V) =
      fst f g ⁻¹' U ∩ snd f g ⁻¹' V := by
  ext z
  constructor
  · rintro ⟨⟨p, hp⟩, t, rfl⟩
    exact ⟨hp.1 ⟨_, rfl⟩, hp.2 ⟨_, rfl⟩⟩
  · intro hz
    obtain ⟨p, t, rfl⟩ := (chartSystem f g).exists_chart z
    obtain ⟨q, hqp, hq, hqt⟩ :=
      exists_patchPair_neighborhood f g hA hB hU hV p t hz.1 hz.2
    obtain ⟨s, hs⟩ := mem_of_mem_nhds hqt
    exact ⟨⟨q, hq⟩, s, ((chartSystem f g).chart_pull hqp s).symm.trans
      (congrArg ((chartSystem f g).chart p) hs)⟩

/-- Each original chart preimage of the subsystem support is open. -/
theorem isOpen_chart_preimage_patchSupport
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    {U : Set A.space} {V : Set B.space} (hU : IsOpen U) (hV : IsOpen V)
    (p : PairIndex f g) :
    IsOpen ((chartSystem f g).chart p ⁻¹'
      (chartSystem f g).subsystemSupport (patchPairs f g U V)) := by
  rw [subsystemSupport_patchPairs f g hA hB hU hV]
  exact ((hU.preimage (continuous_fst f g)).inter
    (hV.preimage (continuous_snd f g))).preimage ((chartSystem f g).continuous_chart p)

/-- The actual support preimages have quasinets of selected subchart images.
In fact each point has one such image as a neighborhood. -/
theorem hasLocalSubchartCover_patchPairs
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    {U : Set A.space} {V : Set B.space} (hU : IsOpen U) (hV : IsOpen V) :
    (chartSystem f g).HasLocalSubchartCover (patchPairs f g U V) := by
  intro p t
  have ht : fst f g ((chartSystem f g).chart p t.val) ∈ U ∧
      snd f g ((chartSystem f g).chart p t.val) ∈ V :=
    (Set.ext_iff.mp (subsystemSupport_patchPairs f g hA hB hU hV)
      ((chartSystem f g).chart p t.val)).mp t.property
  obtain ⟨q, hqp, hq, hqt⟩ :=
    exists_patchPair_neighborhood f g hA hB hU hV p t.val ht.1 ht.2
  let r := (chartSystem f g).relativePull (patchPairs f g U V) ⟨q, hq⟩ p hqp
  have heq : range r =
      (Subtype.val ⁻¹' range ((chartSystem f g).pull hqp) :
        Set ((chartSystem f g).chart p ⁻¹'
          (chartSystem f g).subsystemSupport (patchPairs f g U V))) := by
    ext s
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  have hr : range r ∈ 𝓝 t := by
    rw [heq]
    exact continuous_subtype_val.continuousAt hqt
  refine ⟨{range r}, finite_singleton _, singleton_subset_iff.mpr
    ⟨⟨q, hq⟩, hqp, rfl⟩, ?_, ?_⟩
  · intro F hF
    rw [mem_singleton_iff.mp hF]
    exact mem_of_mem_nhds hr
  · rwa [sUnion_singleton]

/-- Gluing pair charts contained in two open factor patches gives an open
embedding into the unrestricted fibre-product chart quotient. -/
theorem isOpenEmbedding_patchSubsystem
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    {U : Set A.space} {V : Set B.space} (hU : IsOpen U) (hV : IsOpen V) :
    IsOpenEmbedding ((chartSystem f g).subsystemMap (patchPairs f g U V)
      (isDownwardClosed_patchPairs f g U V)) :=
  (chartSystem f g).isOpenEmbedding_subsystemMap (patchPairs f g U V)
    (isDownwardClosed_patchPairs f g U V)
    (isOpen_chart_preimage_patchSupport f g hA hB hU hV)
    (hasLocalSubchartCover_patchPairs f g hA hB hU hV)

end FibreProduct

end Langlands.Analytic
