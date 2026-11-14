import Langlands.Geometry.Building.FacetClosurePullback
import Mathlib.Basic.Sign.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.LeftRightNhds

/-! # Exact facet pullback also gives exact closed-facet pullback -/

noncomputable section

open Filter Topology

namespace Langlands.Geometry.Building.AffineRootSystem

universe uV uA uW uB

variable {V : Type uV} {A : Type uA}
  [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {W : Type uW} {B : Type uB}
  [AddCommGroup W] [Module ℝ W] [AddTorsor W B]

/-- An exact facet pullback along an affine map implies the exact pullback
of that same facet's closed-side closure. -/
theorem preimage_facetClosure_eq_of_preimage_facet_eq
    (f : A →ᵃ[ℝ] B) (Φ : Set (A →ᵃ[ℝ] ℝ)) (Ψ : Set (B →ᵃ[ℝ] ℝ))
    (x : A) (hfacet : f ⁻¹' facet Ψ (f x) = facet Φ x) :
    f ⁻¹' facetClosure Ψ (f x) = facetClosure Φ x := by
  ext y
  change f y ∈ facetClosure Ψ (f x) ↔ y ∈ facetClosure Φ x
  rw [mem_facetClosure_iff_lineMap_mem_facet, mem_facetClosure_iff_lineMap_mem_facet]
  constructor
  · intro h t ht0 ht1
    have hm : f (AffineMap.lineMap y x t) ∈ facet Ψ (f x) := by
      rw [AffineMap.apply_lineMap]
      exact h t ht0 ht1
    change AffineMap.lineMap y x t ∈ f ⁻¹' facet Ψ (f x) at hm
    rwa [hfacet] at hm
  · intro h t ht0 ht1
    have hm : AffineMap.lineMap y x t ∈ f ⁻¹' facet Ψ (f x) := by
      rw [hfacet]
      exact h t ht0 ht1
    change f (AffineMap.lineMap y x t) ∈ facet Ψ (f x) at hm
    rwa [AffineMap.apply_lineMap] at hm

end Langlands.Geometry.Building.AffineRootSystem
