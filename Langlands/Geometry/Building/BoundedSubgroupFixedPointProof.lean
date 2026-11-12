import Langlands.Geometry.Building.BoundedSubgroupFixedPointStatement
import Langlands.Geometry.Building.MetricRealizationProof
import Langlands.Geometry.Metric.KPBoundedSetStabilizerProof
import Langlands.Geometry.Metric.KPNearestPointProof
import Langlands.Geometry.Metric.KPCompleteNPCGeodesicProof
import Langlands.BruhatTits.RationalPoints.BoundedSubgroupNormKernel

/-! # Algebraically bounded subgroups fix points of the actual KP quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {B : ValuationBuildingData G}

local instance boundedFixedAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

namespace MetricRealization

/-- An algebraically bounded set of rational points has bounded orbits. -/
theorem isBounded_image_smul (M : B.MetricRealization)
    {S : Set (rationalPoints G)} (hS : IsAlgebraicallyBounded F G.X S)
    (y : B.ReducedBuilding) :
    letI : MetricSpace B.ReducedBuilding := M.metric
    Bornology.IsBounded ((fun g : rationalPoints G => g • y) '' S) := by
  let : MetricSpace B.ReducedBuilding := M.metric
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have hK : IsCompact (closure S) := hS.isCompact_closure G.X
  have hc : Continuous (fun g : rationalPoints G => g • y) := M.continuous_orbit y
  exact (hK.image hc).isBounded.subset (Set.image_mono subset_closure)

/-- The action of `h` as an isometry equivalence. -/
private def smulIsometry (M : B.MetricRealization) (h : rationalPoints G) :
    letI : MetricSpace B.ReducedBuilding := M.metric
    B.ReducedBuilding ≃ᵢ B.ReducedBuilding :=
  letI : MetricSpace B.ReducedBuilding := M.metric
  haveI := M.isometric
  IsometryEquiv.constSMul h

/-- A subgroup carries one of its orbits onto itself. -/
private theorem image_orbit_eq (H : Subgroup (rationalPoints G)) {h : rationalPoints G}
    (hh : h ∈ H) (y : B.ReducedBuilding) :
    (fun z : B.ReducedBuilding => h • z) ''
        ((fun g : rationalPoints G => g • y) '' (H : Set (rationalPoints G))) =
      (fun g : rationalPoints G => g • y) '' (H : Set (rationalPoints G)) := by
  ext z
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨h * g, H.mul_mem hh hg, mul_smul h g y⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(h⁻¹ * g) • y, ⟨h⁻¹ * g, H.mul_mem (H.inv_mem hh) hg, rfl⟩, ?_⟩
    change h • (h⁻¹ * g) • y = g • y
    rw [smul_smul, mul_inv_cancel_left]

/-- A subgroup preserving a set carries it onto itself. -/
private theorem image_eq_of_forall_mem (H : Subgroup (rationalPoints G)) {h : rationalPoints G}
    (hh : h ∈ H) {Y : Set B.ReducedBuilding} (hY : ∀ h ∈ H, ∀ y ∈ Y, h • y ∈ Y) :
    (fun z : B.ReducedBuilding => h • z) '' Y = Y := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hY h hh y hy
  · intro hz
    refine ⟨h⁻¹ • z, hY h⁻¹ (H.inv_mem hh) z hz, ?_⟩
    change h • h⁻¹ • z = z
    rw [smul_inv_smul]

/-- An algebraically bounded subgroup has a common fixed point. -/
theorem exists_fixed (M : B.MetricRealization) {H : Subgroup (rationalPoints G)}
    (hH : IsAlgebraicallyBounded F G.X (H : Set (rationalPoints G))) :
    ∃ x : B.ReducedBuilding, ∀ h ∈ H, h • x = x := by
  let : MetricSpace B.ReducedBuilding := M.metric
  have := M.complete
  have hNPC := M.nonpositivelyCurved
  have hgeo := Metric.KP.completeNPCGeodesic B.ReducedBuilding hNPC
  obtain ⟨y₀⟩ := (inferInstance : Nonempty B.Apartment)
  let O := (fun g : rationalPoints G => g • B.apartmentMap y₀) '' (H : Set (rationalPoints G))
  have hO : O.Nonempty := ⟨_, 1, H.one_mem, rfl⟩
  obtain ⟨b, hb⟩ := Metric.KP.boundedSetStabilizerFixedPoint B.ReducedBuilding hNPC hgeo O hO
    (M.isBounded_image_smul hH _)
  exact ⟨b, fun h hh => hb (M.smulIsometry h) (image_orbit_eq H hh _)⟩

/-- An algebraically bounded subgroup fixes a point of every nonempty closed convex
subset that it preserves. -/
theorem exists_fixed_mem (M : B.MetricRealization) (H : Subgroup (rationalPoints G))
    (hH : IsAlgebraicallyBounded F G.X (H : Set (rationalPoints G))) :
    letI : MetricSpace B.ReducedBuilding := M.metric
    ∀ Y : Set B.ReducedBuilding, IsClosed Y →
      Langlands.Geometry.Metric.KP.IsGeodesicallyConvex Y →
      (∀ h ∈ H, ∀ y ∈ Y, h • y ∈ Y) →
      ∃ x ∈ Y, ∀ h ∈ H, h • x = x := by
  let : MetricSpace B.ReducedBuilding := M.metric
  have := M.complete
  intro Y hYc hYv hYH
  have hNPC := M.nonpositivelyCurved
  have hgeo := Metric.KP.completeNPCGeodesic B.ReducedBuilding hNPC
  obtain ⟨b, hb⟩ := M.exists_fixed hH
  obtain ⟨π, -, -, -, hπ⟩ :=
    Metric.KP.nearestPointProjection B.ReducedBuilding hNPC hgeo Y hYc hYv
  refine ⟨π b, (π b).2, fun h hh => ?_⟩
  have key := hπ (M.smulIsometry h) (image_eq_of_forall_mem H hh hYH) b
  change (π (h • b) : B.ReducedBuilding) = h • (π b : B.ReducedBuilding) at key
  rw [hb h hh] at key
  exact key.symm

end MetricRealization

end ValuationBuildingData

/-- The local-field form of KP Corollary 4.2.14 on supplied data satisfying the five
axioms of the corrected opening of KP Section 4.2. -/
theorem boundedSubgroupFixedPoint : BoundedSubgroupFixedPointStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro P R T hR hB hT hRR hD hC hTits H hH
  obtain ⟨M⟩ := metricRealization F G hG P R T hR hB hT hRR hD hC hTits
  exact ⟨M.exists_fixed hH, fun M' => M'.exists_fixed_mem H hH⟩

end Langlands.Geometry.Building
