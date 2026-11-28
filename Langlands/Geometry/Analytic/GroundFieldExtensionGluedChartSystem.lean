import Langlands.Geometry.Analytic.AffinoidChartGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionDomainProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionSurjectiveProof

/-! # Ground field extension of a glued affinoid chart system -/

noncomputable section

universe u u' w

namespace Langlands.Analytic.AffinoidChartSystem

open Set PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (D : AffinoidChartSystem.{u, w} K)
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]

local notation "A" => PresentedAffinoidAlgebra.GroundFieldExtension.algebra K L

/-- The actual extended restriction represents the original subchart's
inverse image under the spectrum projection. -/
theorem represents_groundFieldMap {i j : D.Index} (h : D.Sub i j) :
    Represents L (map K L (D.restriction i j h))
      (spectrumProjection K L (D.algebra j) ⁻¹' range (D.pull h)) :=
  domainPreservation K L _ _ _ _ (D.represents i j h)

/-- Extend every bounded chart and every restriction, keeping its index and
containment relation. The subchart meet follows by projecting its point. -/
def extendGroundField : AffinoidChartSystem.{u', w} L where
  Index := D.Index
  algebra i := (A) (D.algebra i)
  Sub := D.Sub
  restriction i j h := map K L (D.restriction i j h)
  sub_refl := D.sub_refl
  sub_trans := D.sub_trans
  restriction_refl i := by rw [D.restriction_refl, map_id]
  restriction_trans hij hjk := by rw [D.restriction_trans, map_comp]
  represents i j h := by
    rw [(D.represents_groundFieldMap L h).2.1]
    exact D.represents_groundFieldMap L h
  meet := by
    intro i j k hik hjk t hi hj
    have hi' : t ∈ spectrumProjection K L (D.algebra k) ⁻¹' range (D.pull hik) :=
      (D.represents_groundFieldMap L hik).2.1 ▸ hi
    have hj' : t ∈ spectrumProjection K L (D.algebra k) ⁻¹' range (D.pull hjk) :=
      (D.represents_groundFieldMap L hjk).2.1 ▸ hj
    obtain ⟨m, hmi, hmj, hm⟩ := D.meet hik hjk (spectrumProjection K L (D.algebra k) t) hi' hj'
    have hm' : t ∈ spectrumProjection K L (D.algebra k) ⁻¹' range (D.pull (D.sub_trans hmi hik)) := hm
    exact ⟨m, hmi, hmj, (D.represents_groundFieldMap L (D.sub_trans hmi hik)).2.1.symm ▸ hm'⟩

private theorem spectrumProjection_pull {i j : D.Index} (h : D.Sub i j)
    (s : BanachSpectrum ((A) (D.algebra i))) :
    spectrumProjection K L (D.algebra j) ((D.extendGroundField L).pull h s) =
      D.pull h (spectrumProjection K L (D.algebra i) s) :=
  spectrumProjection_naturality K L (D.restriction i j h) s

/-- The projection of glued points is the original chart projection on every
summand of the actual quotient. -/
def extensionProjection : C((D.extendGroundField L).Space, D.Space) where
  toFun := Quotient.lift (fun z => D.chart z.1 (spectrumProjection K L (D.algebra z.1) z.2)) (by
    rintro ⟨i, s⟩ ⟨j, t⟩ ⟨k, hki, hkj, v, hvs, hvt⟩
    have hs := (D.spectrumProjection_pull L hki v).symm.trans
      (congrArg (spectrumProjection K L (D.algebra i)) hvs)
    have ht := (D.spectrumProjection_pull L hkj v).symm.trans
      (congrArg (spectrumProjection K L (D.algebra j)) hvt)
    exact D.chart_eq_iff.mpr ⟨k, hki, hkj, _, hs, ht⟩)
  continuous_toFun := by
    apply Continuous.quotient_lift
    refine continuous_sigma fun i => ?_
    exact (D.continuous_chart i).comp (spectrumProjection K L (D.algebra i)).continuous

@[simp]
theorem extensionProjection_chart (i : D.Index) (s : BanachSpectrum ((A) (D.algebra i))) :
    D.extensionProjection L ((D.extendGroundField L).chart i s) =
      D.chart i (spectrumProjection K L (D.algebra i) s) := rfl

/-- A point of an original chart lifts to the extended chart, so the
projection is surjective on the glued quotient. -/
theorem extensionProjection_surjective : Function.Surjective (D.extensionProjection L) := by
  intro t
  obtain ⟨i, x, rfl⟩ := D.exists_chart t
  obtain ⟨z, hz⟩ := spectrumProjection_surjective K L (D.algebra i) x
  exact ⟨(D.extendGroundField L).chart i z, congrArg (D.chart i) hz⟩

/-- The range of an extended chart is the full inverse image of the range
of that original chart, including at points represented in another chart. -/
theorem range_chart_extendGroundField (i : D.Index) :
    range ((D.extendGroundField L).chart i) = D.extensionProjection L ⁻¹' range (D.chart i) := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨spectrumProjection K L (D.algebra i) s, rfl⟩
  · intro ht
    obtain ⟨j, x, rfl⟩ := (D.extendGroundField L).exists_chart t
    obtain ⟨y, hy⟩ := ht
    change D.chart i y = D.chart j (spectrumProjection K L (D.algebra j) x) at hy
    obtain ⟨k, hki, hkj, v, _, hvj⟩ := D.chart_eq_iff.mp hy
    have hx : x ∈ spectrumProjection K L (D.algebra j) ⁻¹' range (D.pull hkj) := ⟨v, hvj⟩
    have hz : x ∈ range ((D.extendGroundField L).pull hkj) :=
      Eq.mpr (congrArg (fun S => x ∈ S) (D.represents_groundFieldMap L hkj).2.1) hx
    obtain ⟨z, hz⟩ := hz
    exact ⟨(D.extendGroundField L).pull hki z,
      (D.extendGroundField L).chart_eq_iff.mpr ⟨k, hki, hkj, z, rfl, hz⟩⟩

end Langlands.Analytic.AffinoidChartSystem
