import Langlands.Geometry.Metric.KPBarycenterProof
import Langlands.Geometry.Metric.KPClosedConvexHullProof

/-! # A common fixed point for the stabilizer of a bounded set -/

open Set Bornology unitInterval

namespace Langlands.Geometry.Metric.KP

universe uX

variable {X : Type*} [MetricSpace X]

/-- Isometric transport preserves the normalized geodesic distance law. -/
theorem IsGeodesic.isometry_map {x y : X} {γ : Path x y} (hγ : IsGeodesic γ)
    (e : X ≃ᵢ X) : IsGeodesic (γ.map e.continuous) := by
  intro s t
  change dist (e (γ s)) (e (γ t)) = dist (e x) (e y) * |(s : ℝ) - t|
  rw [e.dist_eq, e.dist_eq, hγ]

/-- The inverse image under a surjective isometry of a nonempty convex set is convex. -/
theorem IsGeodesicallyConvex.preimage_isometry {M : Set X} (hM : IsGeodesicallyConvex M)
    (e : X ≃ᵢ X) : IsGeodesicallyConvex (e ⁻¹' M) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hM.1
    exact ⟨e.symm x, by simpa using hx⟩
  · intro x hx y hy γ hγ z hz
    obtain ⟨t, rfl⟩ := hz
    exact hM.apply_mem hx hy (hγ.isometry_map e) t

/-- Pulling back each defining superset proves one inclusion for hull transport. -/
theorem isometry_image_closedGeodesicConvexHull_subset (e : X ≃ᵢ X) (M : Set X) :
    e '' closedGeodesicConvexHull M ⊆ closedGeodesicConvexHull (e '' M) := by
  rintro _ ⟨x, hx, rfl⟩
  apply mem_sInter.mpr
  intro C hC
  have hsub : M ⊆ e ⁻¹' C := fun y hy => hC.2.2.2 (mem_image_of_mem e hy)
  have hpre := closedGeodesicConvexHull_subset (hC.1.preimage e.continuous)
    (e.isometry.antilipschitzWith.isBounded_preimage hC.2.1)
    (hC.2.2.1.preimage_isometry e) hsub
  exact hpre hx

/-- The specified intersection of closed bounded convex supersets is covariant under isometries. -/
theorem isometry_image_closedGeodesicConvexHull (e : X ≃ᵢ X) (M : Set X) :
    e '' closedGeodesicConvexHull M = closedGeodesicConvexHull (e '' M) := by
  apply le_antisymm (isometry_image_closedGeodesicConvexHull_subset e M)
  intro x hx
  have hback := isometry_image_closedGeodesicConvexHull_subset e.symm (e '' M)
    (mem_image_of_mem e.symm hx)
  have hcancel : e.symm '' (e '' M) = M := by
    ext y
    simp
  rw [hcancel] at hback
  exact ⟨e.symm x, hback, e.apply_symm_apply x⟩

/-- KP Theorem 1.1.15(2), with one point quantified before all preserving isometries. -/
theorem boundedSetStabilizerFixedPoint : BoundedSetStabilizerFixedPointStatement.{uX} := by
  intro X _ _ hX hgeo M hne hb
  obtain ⟨hclosed, hbounded, hconvex, _⟩ := closedConvexHull X hX hgeo M hne hb
  obtain ⟨hex, hfixed⟩ := barycenter X hX hgeo (closedGeodesicConvexHull M)
    hbounded hclosed hconvex
  obtain ⟨b, hbary, _⟩ := hex
  refine ⟨b, fun e he => hfixed b hbary e ?_⟩
  rw [isometry_image_closedGeodesicConvexHull, he]

end Langlands.Geometry.Metric.KP
