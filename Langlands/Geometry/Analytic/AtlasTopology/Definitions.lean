import Mathlib.Topology.Coherent
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Quasinets and nets for affinoid atlases -/

universe u v

namespace Langlands.Analytic.AtlasTopology

open Set Filter
open scoped Topology

variable {X : Type u} [TopologicalSpace X]

/-- Berkovich's quasinet condition: at every point, finitely many members
all contain the point and their union is a neighborhood of the point. -/
def IsQuasinet (τ : Set (Set X)) : Prop :=
  ∀ x : X, ∃ σ : Set (Set X),
    σ.Finite ∧ σ ⊆ τ ∧ (∀ V ∈ σ, x ∈ V) ∧ ⋃₀ σ ∈ 𝓝 x

/-- Members of a family contained in a subspace, regarded as subsets of
that subspace with its actual induced topology. -/
def restrictedFamily (τ : Set (Set X)) (Y : Set X) : Set (Set Y) :=
  {W | ∃ V ∈ τ, V ⊆ Y ∧ W = Subtype.val ⁻¹' V}

/-- A net is a quasinet whose members contained in each pairwise
intersection form a quasinet of that intersection. -/
def IsNet (τ : Set (Set X)) : Prop :=
  IsQuasinet τ ∧ ∀ U ∈ τ, ∀ V ∈ τ,
    IsQuasinet (restrictedFamily τ (U ∩ V))

/-- In the source, "compact" includes Hausdorffness. Both requirements
are explicit because the ambient space need not be Hausdorff. -/
def IsCompactFamily (τ : Set (Set X)) : Prop :=
  ∀ V ∈ τ, IsCompact V ∧ T2Space V

/-- The actual family of rectangles obtained from two families. -/
def productFamily {Y : Type v} (τ : Set (Set X)) (υ : Set (Set Y)) :
    Set (Set (X × Y)) :=
  {W | ∃ U ∈ τ, ∃ V ∈ υ, W = U ×ˢ V}

end Langlands.Analytic.AtlasTopology
