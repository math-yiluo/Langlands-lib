import Langlands.Geometry.Analytic.AtlasTopology.Definitions
import Mathlib.Topology.LocallyClosed

/-! # Exact topology target for compact affinoid atlases -/

universe u v

namespace Langlands.Analytic.AtlasTopology

open Set

/-- The topology determined by a quasinet, the compact-member Hausdorff
criterion, and local closedness of intersections in a compact net. -/
def QuasinetTopologyStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (Y : Type v) [TopologicalSpace Y],
    IsNet ({univ} : Set (Set X)) ∧
    (∀ τ : Set (Set X), IsQuasinet τ →
      (⋃₀ τ = univ) ∧
      (∀ υ : Set (Set X), τ ⊆ υ → IsQuasinet υ) ∧
      Topology.IsCoherentWith τ ∧
      (∀ U : Set X, IsOpen U ↔ ∀ V ∈ τ, IsOpen (Subtype.val ⁻¹' U : Set V)) ∧
      (∀ U : Set X, IsClosed U ↔ ∀ V ∈ τ, IsClosed (Subtype.val ⁻¹' U : Set V)) ∧
      (∀ f : X → Y, Continuous f ↔ ∀ V ∈ τ, ContinuousOn f V) ∧
      (∀ υ : Set (Set Y), IsQuasinet υ → IsQuasinet (productFamily τ υ)) ∧
      (IsCompactFamily τ →
        (T2Space X ↔ ∀ U ∈ τ, ∀ V ∈ τ, IsCompact (U ∩ V))) ∧
      ((∀ V ∈ τ, IsCompact V) → WeaklyLocallyCompactSpace X) ∧
      ((∀ V ∈ τ, IsCompact V) → T2Space X → LocallyCompactSpace X)) ∧
    (∀ τ : Set (Set X), IsNet τ → IsCompactFamily τ →
      ∀ U ∈ τ, ∀ V ∈ τ,
        LocallyCompactSpace ↥(U ∩ V) ∧
        IsLocallyClosed (Subtype.val ⁻¹' V : Set U) ∧
        IsLocallyClosed (Subtype.val ⁻¹' U : Set V))

end Langlands.Analytic.AtlasTopology
