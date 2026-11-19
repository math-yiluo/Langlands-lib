import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionDomainProof
import Langlands.Geometry.Analytic.AffinoidProductChartSystem
import Langlands.Geometry.Analytic.AffinoidChartLift

/-! # The quotient chart system for extension of the ground field -/

noncomputable section

universe u v w u'

namespace Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

open Set Topology PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Scalar extension of an original chart algebra, preserving arity and radii. -/
abbrev chartAlgebra (i : a.Index) : PresentedAffinoidAlgebra L :=
  PresentedAffinoidAlgebra.GroundFieldExtension.algebra K L (a.algebra i)

/-- The scalar extension of an original bounded restriction map. -/
def restriction (i j : a.Index) (h : range (a.chart i) ⊆ range (a.chart j)) :
    BoundedAlgHom L (chartAlgebra K L a j) (chartAlgebra K L a i) :=
  map K L (a.restriction i j h)

/-- The affinoid domain theorem identifies the extended restriction locus. -/
theorem restriction_represents (i j : a.Index)
    (h : range (a.chart i) ⊆ range (a.chart j)) :
    Represents L (restriction K L a i j h)
      (spectrumProjection K L (a.algebra j) ⁻¹' (a.chart j ⁻¹' range (a.chart i))) :=
  domainPreservation.{u, u'} K L _ _ _ _ (a.restriction_represents i j h)

theorem mem_range_restriction_iff (i j : a.Index)
    (h : range (a.chart i) ⊆ range (a.chart j))
    (t : BanachSpectrum (chartAlgebra K L a j)) :
    t ∈ range (BanachSpectrum.comap (restriction K L a i j h).toBoundedRingHom) ↔
      a.chart j (spectrumProjection K L (a.algebra j) t) ∈ range (a.chart i) := by
  rw [(restriction_represents K L a i j h).2.1]
  rfl

theorem restriction_refl (i : a.Index) :
    restriction K L a i i subset_rfl = BoundedAlgHom.id L _ := by
  unfold restriction
  rw [a.restriction_id, map_id]

theorem restriction_trans {i j k : a.Index}
    (hij : range (a.chart i) ⊆ range (a.chart j))
    (hjk : range (a.chart j) ⊆ range (a.chart k)) :
    restriction K L a i k (hij.trans hjk) =
      (restriction K L a i j hij).comp (restriction K L a j k hjk) := by
  unfold restriction
  rw [a.restriction_comp i j k hij hjk, map_comp]

/-- Original indices and containments, with scalar-extended chart algebras
and restrictions. -/
abbrev chartSystem : AffinoidChartSystem.{u', w} L where
  Index := a.Index
  algebra := chartAlgebra K L a
  Sub i j := range (a.chart i) ⊆ range (a.chart j)
  restriction := restriction K L a
  sub_refl _ := subset_rfl
  sub_trans := Subset.trans
  restriction_refl := restriction_refl K L a
  restriction_trans := restriction_trans K L a
  represents i j h := by
    rw [(restriction_represents K L a i j h).2.1]
    exact restriction_represents K L a i j h
  meet := by
    intro i j k hik hjk t hti htj
    rw [mem_range_restriction_iff K L a] at hti htj
    obtain ⟨m, hm, hxm⟩ := exists_chart_inter (a := a) hti htj
    refine ⟨m, hm.trans inter_subset_left, hm.trans inter_subset_right, ?_⟩
    exact (mem_range_restriction_iff K L a m k _ t).2 hxm

/-- Chartwise naturality with respect to original domain inclusions. -/
theorem chart_projection_pull (i j : a.Index)
    (h : range (a.chart i) ⊆ range (a.chart j))
    (s : BanachSpectrum (chartAlgebra K L a i)) :
    a.chart j (spectrumProjection K L (a.algebra j)
      ((chartSystem K L a).pull h s)) =
        a.chart i (spectrumProjection K L (a.algebra i) s) := by
  rw [show (chartSystem K L a).pull h s =
    BanachSpectrum.comap (map K L (a.restriction i j h)).toBoundedRingHom s from rfl,
    spectrumProjection_naturality]
  exact a.restriction_chart i j h _

/-- The glued projection to the original space, obtained by quotient descent. -/
def projection : (chartSystem K L a).Space → X :=
  Quotient.lift (fun z => a.chart z.1 (spectrumProjection K L (a.algebra z.1) z.2)) (by
    rintro ⟨i, s⟩ ⟨j, t⟩ ⟨k, hki, hkj, v, hvs, hvt⟩
    change a.chart i (spectrumProjection K L (a.algebra i) s) =
      a.chart j (spectrumProjection K L (a.algebra j) t)
    have hi := chart_projection_pull K L a k i hki v
    have hj := chart_projection_pull K L a k j hkj v
    rw [hvs] at hi
    rw [hvt] at hj
    exact hi.trans hj.symm)

theorem projection_chart (i : a.Index) (s : BanachSpectrum (chartAlgebra K L a i)) :
    projection K L a ((chartSystem K L a).chart i s) =
      a.chart i (spectrumProjection K L (a.algebra i) s) := rfl

theorem continuous_projection : Continuous (projection K L a) := by
  apply Continuous.quotient_lift
  refine continuous_sigma fun i => ?_
  exact (a.isEmbedding_chart i).continuous.comp (spectrumProjection K L (a.algebra i)).continuous

/-- The actual quotient chart domains are precisely the projection preimages
of the original domains. -/
theorem range_chart (i : a.Index) :
    range ((chartSystem K L a).chart i) =
      projection K L a ⁻¹' range (a.chart i) := by
  let C := chartSystem K L a
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, (projection_chart K L a i s).symm⟩
  · intro hz
    obtain ⟨j, t, rfl⟩ := C.exists_chart z
    change a.chart j (spectrumProjection K L (a.algebra j) t) ∈ range (a.chart i) at hz
    obtain ⟨m, hm, hxm⟩ := exists_chart_inter (a := a) hz ⟨_, rfl⟩
    have hmi := hm.trans inter_subset_left
    have hmj := hm.trans inter_subset_right
    obtain ⟨s, hs⟩ := (mem_range_restriction_iff K L a m j hmj t).2 hxm
    refine ⟨C.pull hmi s, ?_⟩
    have hs' : C.pull hmj s = t := hs
    rw [C.chart_pull hmi s, ← C.chart_pull hmj s, hs']

/-- The generic chart-lift topology applies to the constructed quotient. -/
def atlasProjection : (chartSystem K L a).AtlasProjection a where
  chartIndex := Equiv.refl _
  pointMap := ⟨projection K L a, continuous_projection K L a⟩
  chartPoint i := spectrumProjection K L (a.algebra i)
  pointMap_chart := projection_chart K L a
  range_chart := range_chart K L a
  sub_of_subset _ _ h := h

end Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension
