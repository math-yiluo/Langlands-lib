/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.TruncGE
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.TruncLE

/-!
# Truncations of cochain complexes: behaviour on degrees

Supplement to `Mathlib.Algebra.Homology.Embedding.CochainComplex`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Category Limits ComplexShape ZeroObject

namespace CochainComplex

variable {C : Type*} [Category* C]

open HomologicalComplex

variable [HasZeroMorphisms C] (K : CochainComplex C ℤ)
  [HasZeroObject C] [∀ i, K.HasHomology i]

instance (n : ℤ) : Mono (K.ιTruncLE n) := by
  dsimp only [ιTruncLE]
  infer_instance

instance (n : ℤ) : Epi (K.πTruncGE n) := by
  dsimp only [πTruncGE]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
lemma isIso_ιTruncLE_f (n m : ℤ) (h : m < n) : IsIso ((K.ιTruncLE n).f m) := by
  obtain ⟨a, rfl⟩ : ∃ a, (embeddingUpIntLE n).f a = m := by
    obtain ⟨a, ha⟩ := Int.le.dest h.le
    exact ⟨a, by dsimp; omega⟩
  apply HomologicalComplex.isIso_ιTruncLE_f
  simp only [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
  rintro rfl
  simp at h

set_option backward.defeqAttrib.useBackward true in
lemma isIso_πTruncGE_f (n m : ℤ) (h : n < m) : IsIso ((K.πTruncGE n).f m) := by
  obtain ⟨a, rfl⟩ : ∃ a, (embeddingUpIntGE n).f a = m := by
    obtain ⟨a, ha⟩ := Int.le.dest h.le
    exact ⟨a, by dsimp; omega⟩
  apply HomologicalComplex.isIso_πTruncGE_f
  simp only [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
  rintro rfl
  simp at h

end CochainComplex
