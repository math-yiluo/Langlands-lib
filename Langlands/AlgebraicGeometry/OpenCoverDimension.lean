import Mathlib.Topology.KrullDimension

/-! # Irreducible closed chains on open charts -/

universe u v

open Set Order TopologicalSpace Topology

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {X : Type u} [TopologicalSpace X]

/-- Restrict an actual strict chain of irreducible closed subsets to an
open chart meeting its smallest member. -/
noncomputable def restrictIrreducibleClosedSeries
    (U : Opens X) (p : LTSeries (IrreducibleCloseds X))
    (hne : ((Subtype.val : U → X) ⁻¹' (p.head : Set X)).Nonempty) :
    LTSeries (IrreducibleCloseds U) :=
  LTSeries.mk p.length
    (fun i => (IrreducibleCloseds.orderIsoOfIsOpenEmbedding
      (Subtype.val : U → X) U.isOpen.isOpenEmbedding_subtypeVal).symm
        ⟨p i, by
          obtain ⟨x, hx⟩ := hne
          exact ⟨x, p.head_le i hx⟩⟩)
    (fun i j hij => (IrreducibleCloseds.orderIsoOfIsOpenEmbedding
      (Subtype.val : U → X) U.isOpen.isOpenEmbedding_subtypeVal).symm.strictMono
        (p.strictMono hij))

@[simp]
theorem restrictIrreducibleClosedSeries_length
    (U : Opens X) (p : LTSeries (IrreducibleCloseds X))
    (hne : ((Subtype.val : U → X) ⁻¹' (p.head : Set X)).Nonempty) :
    (restrictIrreducibleClosedSeries U p hne).length = p.length := rfl

@[simp]
theorem restrictIrreducibleClosedSeries_coe
    (U : Opens X) (p : LTSeries (IrreducibleCloseds X))
    (hne : ((Subtype.val : U → X) ⁻¹' (p.head : Set X)).Nonempty)
    (i : Fin (p.length + 1)) :
    ((restrictIrreducibleClosedSeries U p hne) i : Set U) =
      (Subtype.val : U → X) ⁻¹' (p i : Set X) := rfl

/-- The actual topological dimension is computed on any open cover. -/
theorem topologicalKrullDim_eq_iSup_openCover
    {ι : Type v} (U : ι → Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (U i) := by
  apply le_antisymm
  · change (⨆ p : LTSeries (IrreducibleCloseds X), (p.length : WithBot ℕ∞)) ≤ _
    refine iSup_le fun p => ?_
    obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
    obtain ⟨i, hi⟩ := hcover x
    let q := restrictIrreducibleClosedSeries (U i) p ⟨⟨x, hi⟩, hx⟩
    have hlen : (p.length : WithBot ℕ∞) ≤ topologicalKrullDim (U i) :=
      q.length_le_krullDim
    exact hlen.trans (le_iSup (fun j => topologicalKrullDim (U j)) i)
  · exact iSup_le fun i => topologicalKrullDim_subspace_le X (U i)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
