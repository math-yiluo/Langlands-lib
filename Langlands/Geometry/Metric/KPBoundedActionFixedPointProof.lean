import Langlands.Geometry.Metric.KPBoundedSetStabilizerProof
import Langlands.Geometry.Metric.KPCompleteNPCGeodesicProof

/-! # Fixed points of bounded isometric group actions (KP Corollary 1.1.19) -/

open Set Bornology

namespace Langlands.Geometry.Metric.KP

universe uX uG

/-- Each group element maps an orbit, viewed as an image of the whole group, onto itself. -/
theorem constSMul_image_orbit {G : Type*} {X : Type*} [Group G] [MetricSpace X]
    [MulAction G X] [IsIsometricSMul G X] (g : G) (x : X) :
    IsometryEquiv.constSMul g '' ((fun h : G => h • x) '' univ) =
      (fun h : G => h • x) '' univ := by
  ext y
  constructor
  · rintro ⟨_, ⟨h, -, rfl⟩, rfl⟩
    exact ⟨g * h, mem_univ _, mul_smul g h x⟩
  · rintro ⟨h, -, rfl⟩
    refine ⟨(g⁻¹ * h) • x, ⟨g⁻¹ * h, mem_univ _, rfl⟩, ?_⟩
    change g • (g⁻¹ * h) • x = h • x
    rw [smul_smul, mul_inv_cancel_left]

/-- KP Corollary 1.1.19: an isometric action of an arbitrary group on a nonempty complete NPC
metric space with a bounded orbit has a fixed point. Geodesics are constructed, not assumed. -/
theorem boundedActionFixedPoint : BoundedActionFixedPointStatement.{uX, uG} := by
  intro X _ _ _ hX G _ _ _ hbdd
  obtain ⟨x, hx⟩ := hbdd
  have hgeo : IsGeodesicSpace X := completeNPCGeodesic X hX
  obtain ⟨b, hb⟩ := boundedSetStabilizerFixedPoint X hX hgeo ((fun h : G => h • x) '' univ)
    ⟨x, 1, mem_univ _, one_smul G x⟩ hx
  exact ⟨b, fun g => hb (IsometryEquiv.constSMul g) (constSMul_image_orbit g x)⟩

end Langlands.Geometry.Metric.KP
