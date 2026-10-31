import Langlands.Geometry.Analytic.AtlasTopology.Refinement

/-! # Composition of finite relative local refinements -/

universe u

namespace Langlands.Analytic.AtlasTopology

open Set Filter
open scoped Topology

variable {X : Type u} [TopologicalSpace X]

/-- Enlarging the refining family and shrinking the refined family retain
all the finite relative neighborhood witnesses. -/
theorem LocallyRefines.mono {υ τ υ' τ' : Set (Set X)}
    (h : LocallyRefines υ τ) (hυ : υ ⊆ υ') (hτ : τ' ⊆ τ) :
    LocallyRefines υ' τ' := by
  intro U hU x hx
  obtain ⟨σ, hf, hs, hm, hn⟩ := h U (hτ hU) x hx
  exact ⟨σ, hf, hs.trans hυ, hm, hn⟩

/-- Finite relative local refinements compose by taking the finite union
of the second-stage witnesses inside a first-stage witness. -/
theorem LocallyRefines.trans {τ υ κ : Set (Set X)}
    (h : LocallyRefines υ τ) (g : LocallyRefines κ υ) : LocallyRefines κ τ := by
  classical
  intro U hU x hx
  obtain ⟨ξ, hξ, hξυ, hmξ, hnξ⟩ := h U hU x hx
  have hw : ∀ V : ξ, ∃ σ : Set (Set X),
      σ.Finite ∧ σ ⊆ κ ∧ (∀ W ∈ σ, W ⊆ V.val ∧ x ∈ W) ∧
        ⋃₀ σ ∈ 𝓝[V.val] x :=
    fun V => g V.val (hξυ V.property) x (hmξ V.val V.property).2
  choose σ hf hs hm hn using hw
  let : Fintype ξ := hξ.fintype
  let δ : Set (Set X) := ⋃ V : ξ, σ V
  refine ⟨δ, finite_iUnion hf, ?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨V, hWV⟩ := mem_iUnion.mp hW
    exact hs V hWV
  · intro W hW
    obtain ⟨V, hWV⟩ := mem_iUnion.mp hW
    exact ⟨(hm V W hWV).1.trans (hmξ V.val V.property).1, (hm V W hWV).2⟩
  · apply (nhdsWithin_le_of_mem hnξ)
    rw [nhdsWithin_sUnion hξ x]
    apply Filter.mem_iSup.mpr
    intro V
    apply Filter.mem_iSup.mpr
    intro hV
    apply Filter.mem_of_superset (hn ⟨V, hV⟩)
    rintro y ⟨W, hW, hy⟩
    exact ⟨W, mem_iUnion.mpr ⟨⟨V, hV⟩, hW⟩, hy⟩

end Langlands.Analytic.AtlasTopology
