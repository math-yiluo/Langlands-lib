import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.KrullDimension

/-! # A specialization chain from Krull dimension at least two -/

universe u

open AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.KrullDimensionChain

/-- **Chains from dimension.** A quasi-compact scheme of topological Krull dimension greater
than one has points `y₀ ⤳ y₁ ⤳ z` with `y₀ ≠ y₁`, `y₁ ≠ z` and `z` a closed point. -/
theorem exists_chain_of_not_le_one {X : Scheme.{u}} [CompactSpace X]
    (h : ¬ topologicalKrullDim X ≤ 1) :
    ∃ y₀ y₁ z : X, y₀ ⤳ y₁ ∧ y₁ ⤳ z ∧ y₀ ≠ y₁ ∧ y₁ ≠ z ∧ IsClosed ({z} : Set X) := by
  rw [topologicalKrullDim, Order.krullDim_le_one_iff] at h
  simp only [not_forall, not_or] at h
  obtain ⟨B, hBmin, hBmax⟩ := h
  obtain ⟨A, hAB⟩ := not_isMin_iff.mp hBmin
  obtain ⟨C, hBC⟩ := not_isMax_iff.mp hBmax
  have hgen : ∀ Z : TopologicalSpace.IrreducibleCloseds X,
      IsGenericPoint Z.isIrreducible.genericPoint (Z : Set X) :=
    fun Z ↦ Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed
  have hAB' : (A : Set X) ⊆ B := hAB.le
  have hBC' : (B : Set X) ⊆ C := hBC.le
  obtain ⟨z, hzA, hz⟩ := A.isClosed.exists_closed_singleton A.isIrreducible.nonempty
  refine ⟨C.isIrreducible.genericPoint, B.isIrreducible.genericPoint, z, ?_, ?_, ?_, ?_, hz⟩
  · exact (hgen C).specializes_iff_mem.mpr (hBC' (hgen B).mem)
  · exact (hgen B).specializes_iff_mem.mpr (hAB' hzA)
  · intro he
    apply hBC.ne
    apply SetLike.coe_injective
    rw [← isGenericPoint_def.mp (hgen B), ← isGenericPoint_def.mp (hgen C), he]
  · intro he
    apply hAB.ne
    apply SetLike.coe_injective
    apply le_antisymm hAB'
    rw [← isGenericPoint_def.mp (hgen B), he, hz.closure_eq]
    exact Set.singleton_subset_iff.mpr hzA

end Langlands.AlgebraicGeometry.KrullDimensionChain
