import Langlands.Geometry.Analytic.GroundFieldExtensionAtlas
import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionTower

/-! # Direct and successive ground field extension of affinoid atlas spaces -/

noncomputable section

universe u u' u'' v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

open Set Topology
open PresentedAffinoidAlgebra.GroundFieldExtension

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  (M : Type u'') [NormedField M] [IsUltrametricDist M] [CompleteSpace M]
  [NormedAlgebra L M] [NormedAlgebra K M] [IsScalarTower K L M]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

local notation "D" => chartSystem K M a
local notation "S" => chartSystem L M (atlas K L a)

/-- The component homeomorphism on the actual extended chart spectra. -/
abbrev towerChartHomeomorph (i : a.Index) :
    BanachSpectrum ((D).algebra i) ≃ₜ BanachSpectrum ((S).algebra i) :=
  towerSpectrumHomeomorph K L M (a.algebra i)

omit [IsScalarTower K L M] in
/-- The successive chart system has the same containments as the direct one. -/
theorem towerSub_iff (i j : a.Index) : (S).Sub i j ↔ (D).Sub i j :=
  range_chart_subset_iff K L a i j

/-- The component homeomorphisms intertwine all chart restriction comaps. -/
theorem towerChartHomeomorph_pull (i j : a.Index) (h : (D).Sub i j)
    (s : BanachSpectrum ((D).algebra i)) :
    towerChartHomeomorph K L M a j ((D).pull h s) =
      (S).pull ((towerSub_iff K L M a i j).2 h) (towerChartHomeomorph K L M a i s) :=
  towerSpectrumHomeomorph_naturality K L M (a.restriction i j h) s

/-- A common-subchart witness is transported to the same index. Conversely,
the component inverse recovers a direct witness at that index. -/
theorem towerGlued_iff (i j : a.Index) (s : BanachSpectrum ((D).algebra i))
    (t : BanachSpectrum ((D).algebra j)) :
    (D).Glued i s j t ↔ (S).Glued i (towerChartHomeomorph K L M a i s)
      j (towerChartHomeomorph K L M a j t) := by
  constructor
  · rintro ⟨k, hki, hkj, r, hi, hj⟩
    refine ⟨k, (towerSub_iff K L M a k i).2 hki, (towerSub_iff K L M a k j).2 hkj,
      towerChartHomeomorph K L M a k r, ?_, ?_⟩
    · exact (towerChartHomeomorph_pull K L M a k i hki r).symm.trans
        (congrArg (towerChartHomeomorph K L M a i) hi)
    · exact (towerChartHomeomorph_pull K L M a k j hkj r).symm.trans
        (congrArg (towerChartHomeomorph K L M a j) hj)
  · rintro ⟨k, hki, hkj, r, hi, hj⟩
    let r₀ := (towerChartHomeomorph K L M a k).symm r
    have hr : towerChartHomeomorph K L M a k r₀ = r :=
      (towerChartHomeomorph K L M a k).apply_symm_apply r
    let hki₀ := (towerSub_iff K L M a k i).1 hki
    let hkj₀ := (towerSub_iff K L M a k j).1 hkj
    refine ⟨k, hki₀, hkj₀, r₀, ?_, ?_⟩
    · apply (towerChartHomeomorph K L M a i).injective
      exact (towerChartHomeomorph_pull K L M a k i hki₀ r₀).trans
        ((congrArg ((S).pull hki) hr).trans hi)
    · apply (towerChartHomeomorph K L M a j).injective
      exact (towerChartHomeomorph_pull K L M a k j hkj₀ r₀).trans
        ((congrArg ((S).pull hkj) hr).trans hj)

private def towerPointMap : (D).Space → (S).Space :=
  Quotient.lift (fun p => (S).chart p.1 (towerChartHomeomorph K L M a p.1 p.2)) (by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    exact (S).chart_eq_iff.2 ((towerGlued_iff K L M a i j s t).1 h))

private def towerPointInv : (S).Space → (D).Space :=
  Quotient.lift (fun p => (D).chart p.1 ((towerChartHomeomorph K L M a p.1).symm p.2)) (by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    apply (D).chart_eq_iff.2
    apply (towerGlued_iff K L M a i j _ _).2
    change (S).Glued i s j t at h
    simpa only [Homeomorph.apply_symm_apply] using h)

/-- The actual glued direct extension and the actual glued successive
extension are homeomorphic, by descent of the component homeomorphisms. -/
def towerHomeomorph : (D).Space ≃ₜ (S).Space where
  toFun := towerPointMap K L M a
  invFun := towerPointInv K L M a
  left_inv z := by
    obtain ⟨i, s, rfl⟩ := (D).exists_chart z
    exact congrArg ((D).chart i) ((towerChartHomeomorph K L M a i).symm_apply_apply s)
  right_inv z := by
    obtain ⟨i, s, rfl⟩ := (S).exists_chart z
    exact congrArg ((S).chart i) ((towerChartHomeomorph K L M a i).apply_symm_apply s)
  continuous_toFun := by
    apply Continuous.quotient_lift
    refine continuous_sigma fun i => ?_
    exact ((S).continuous_chart i).comp (towerChartHomeomorph K L M a i).continuous
  continuous_invFun := by
    apply Continuous.quotient_lift
    refine continuous_sigma fun i => ?_
    exact ((D).continuous_chart i).comp (towerChartHomeomorph K L M a i).symm.continuous

@[simp] theorem towerHomeomorph_chart (i : a.Index) (s : BanachSpectrum ((D).algebra i)) :
    towerHomeomorph K L M a ((D).chart i s) = (S).chart i (towerChartHomeomorph K L M a i s) := rfl

@[simp] theorem towerHomeomorph_symm_chart (i : a.Index) (s : BanachSpectrum ((S).algebra i)) :
    (towerHomeomorph K L M a).symm ((S).chart i s) =
      (D).chart i ((towerChartHomeomorph K L M a i).symm s) := rfl

/-- The comparison sends each direct chart domain onto its successive counterpart. -/
theorem towerHomeomorph_image_chart (i : a.Index) :
    towerHomeomorph K L M a '' range ((D).chart i) = range ((S).chart i) := by
  ext z
  constructor
  · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨towerChartHomeomorph K L M a i s, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨(D).chart i ((towerChartHomeomorph K L M a i).symm t), ⟨_, rfl⟩,
      congrArg ((S).chart i) ((towerChartHomeomorph K L M a i).apply_symm_apply t)⟩

/-- The composite of the actual successive projections agrees with the
actual direct projection. -/
theorem towerHomeomorph_projection (z : (D).Space) :
    projection K L a (projection L M (atlas K L a) (towerHomeomorph K L M a z)) =
      projection K M a z := by
  obtain ⟨i, s, rfl⟩ := (D).exists_chart z
  exact congrArg (a.chart i) (towerSpectrumHomeomorph_projection K L M (a.algebra i) s)

end Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension
