import Langlands.AlgebraicGeometry.ComponentOpenDimension
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Krull dimension at a point of an actual topological space -/

noncomputable section

universe u v

open Set Order Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The minimum of the dimensions of the actual open neighbourhoods of a point. -/
def topologicalKrullDimAt (x : X) : WithBot ℕ∞ :=
  sInf {r | ∃ U : Opens X, x ∈ U ∧ topologicalKrullDim U = r}

/-- The infimum in the definition is attained, even when it is infinite. -/
theorem exists_open_topologicalKrullDim_eq_at (x : X) :
    ∃ U : Opens X, x ∈ U ∧ topologicalKrullDim U = topologicalKrullDimAt x := by
  exact csInf_mem (show {r | ∃ U : Opens X, x ∈ U ∧
    topologicalKrullDim U = r}.Nonempty from ⟨_, ⊤, trivial, rfl⟩)

theorem topologicalKrullDimAt_le_open (x : X) (U : Opens X) (hx : x ∈ U) :
    topologicalKrullDimAt x ≤ topologicalKrullDim U :=
  sInf_le ⟨U, hx, rfl⟩

theorem topologicalKrullDimAt_le (x : X) :
    topologicalKrullDimAt x ≤ topologicalKrullDim X :=
  (topologicalKrullDimAt_le_open x ⊤ trivial).trans_eq
    ((Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq _)

/-- Global dimension is the supremum of these local dimensions, including
the empty-space case. -/
theorem topologicalKrullDim_eq_iSup_at :
    topologicalKrullDim X = ⨆ x : X, topologicalKrullDimAt x := by
  choose U hx hU using fun x : X => exists_open_topologicalKrullDim_eq_at x
  exact (topologicalKrullDim_eq_iSup_openCover U (fun x => ⟨x, hx x⟩)).trans
    (iSup_congr hU)

/-- A bound on the local dimension is witnessed by an actual open neighbourhood. -/
theorem topologicalKrullDimAt_le_iff (x : X) (r : WithBot ℕ∞) :
    topologicalKrullDimAt x ≤ r ↔
      ∃ U : Opens X, x ∈ U ∧ topologicalKrullDim U ≤ r := by
  constructor
  · intro h
    obtain ⟨U, hx, hU⟩ := exists_open_topologicalKrullDim_eq_at x
    exact ⟨U, hx, hU.trans_le h⟩
  · rintro ⟨U, hx, hU⟩
    exact (topologicalKrullDimAt_le_open x U hx).trans hU

/-- Open embeddings preserve dimension at each actual point. -/
theorem topologicalKrullDimAt_eq_of_isOpenEmbedding
    {f : X → Y} (hf : IsOpenEmbedding f) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x) := by
  apply le_antisymm
  · obtain ⟨V, hx, hV⟩ := exists_open_topologicalKrullDim_eq_at (f x)
    let U : Opens X := ⟨f ⁻¹' V, V.isOpen.preimage hf.continuous⟩
    have hdim : topologicalKrullDim U ≤ topologicalKrullDim V := by
      exact ((hf.isEmbedding.homeomorphImage (U : Set X)).isHomeomorph.topologicalKrullDim_eq _).trans_le
        ((Topology.IsEmbedding.inclusion
          (show f '' (U : Set X) ⊆ V from fun y ⟨z, hz, hzy⟩ => hzy ▸ hz)).isInducing.topologicalKrullDim_le)
    exact (topologicalKrullDimAt_le_open x U hx).trans (hdim.trans_eq hV)
  · obtain ⟨U, hx, hU⟩ := exists_open_topologicalKrullDim_eq_at x
    let V : Opens Y := ⟨f '' (U : Set X), hf.isOpenMap _ U.isOpen⟩
    have hdim : topologicalKrullDim U = topologicalKrullDim V :=
      (hf.isEmbedding.homeomorphImage (U : Set X)).isHomeomorph.topologicalKrullDim_eq _
    exact (topologicalKrullDimAt_le_open (f x) V ⟨x, hx, rfl⟩).trans_eq
      (hdim.symm.trans hU)

theorem topologicalKrullDimAt_open (U : Opens X) (x : U) :
    topologicalKrullDimAt x = topologicalKrullDimAt (x : X) :=
  topologicalKrullDimAt_eq_of_isOpenEmbedding U.isOpenEmbedding' x

theorem topologicalKrullDimAt_homeomorph (e : X ≃ₜ Y) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (e x) :=
  topologicalKrullDimAt_eq_of_isOpenEmbedding e.isOpenEmbedding x

/-- On a fixed space the local-dimension sublevels are open. This does not
assert openness of relative fibre dimension on a varying family. -/
theorem isOpen_topologicalKrullDimAt_le (r : WithBot ℕ∞) :
    IsOpen {x : X | topologicalKrullDimAt x ≤ r} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hxU, hU⟩ := (topologicalKrullDimAt_le_iff x r).mp hx
  exact ⟨U, fun y hy => (topologicalKrullDimAt_le_open y U hy).trans hU,
    U.isOpen, hxU⟩

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
