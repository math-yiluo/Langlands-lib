/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! Strict closed-complement part of the nonempty support induction step. -/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The closed complement of a nonempty open piece has strictly smaller support.

Source: `ModuleObject/Colimit/TwoColimit.lean`, support-induction split.
Proof: take `Z` to be the scheme-theoretic closed complement of `j`. The complement
identities give the cover and disjointness. Since `j` is nonempty and `i` is a closed
immersion, its image misses the image of a point of `U`; the image of `Z` is therefore a
proper closed subset of the support `D` and is represented by a `D' < D`.
(auxiliary; not a blueprint node)
-/
theorem exists_strict_closed_complement_support
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T]
    (D : TopologicalSpace.Closeds T)
    (Y : Scheme.{u}) (i : Y ⟶ T) [IsClosedImmersion i] [Nonempty Y]
    (hYi : Set.range i ⊆ D)
    (U : Scheme.{u}) (j : U ⟶ Y) [IsOpenImmersion j] [Nonempty U] :
    ∃ (Z : Scheme.{u}) (k : Z ⟶ Y), IsClosedImmersion k ∧
      Set.range j ∪ Set.range k = Set.univ ∧
      Disjoint (Set.range j) (Set.range k) ∧
      ∃ (D' : TopologicalSpace.Closeds T), D' < D ∧ Set.range (k ≫ i) ⊆ D' := by
  let k := j.closedComplement
  let D' : TopologicalSpace.Closeds T :=
    ⟨Set.range (k ≫ i).base, (k ≫ i).isClosedEmbedding.isClosed_range⟩
  have hlt : D' < D := by
    refine lt_of_le_of_ne ?_ fun h ↦ ?_
    · rintro _ ⟨z, rfl⟩
      exact hYi ⟨k z, rfl⟩
    · obtain ⟨u⟩ := ‹Nonempty U›
      have hmem : i (j u) ∈ (D' : Set T) := by
        rw [h]
        exact hYi ⟨j u, rfl⟩
      obtain ⟨z, hz⟩ := hmem
      have hz' : k z = j u := i.isClosedEmbedding.injective (by simpa using hz)
      have hzmem : k z ∈ Set.range k := ⟨z, rfl⟩
      change k z ∈ Set.range j.closedComplement.base at hzmem
      rw [j.range_closedComplement, hz'] at hzmem
      exact hzmem ⟨u, rfl⟩
  refine ⟨_, k, inferInstance, ?_, ?_, D', hlt, Set.Subset.rfl⟩
  · change Set.range j.base ∪ Set.range j.closedComplement.base = Set.univ
    rw [j.range_closedComplement, Set.union_compl_self]
  · change Disjoint (Set.range j.base) (Set.range j.closedComplement.base)
    rw [j.range_closedComplement]
    exact disjoint_compl_right

end AlgebraicGeometry.ProEtale
