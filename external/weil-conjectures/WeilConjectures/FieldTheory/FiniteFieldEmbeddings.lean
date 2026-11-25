/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Embeddings of a finite field

Let `K ⊆ L` be finite fields and `M` a field over `K`. Every `K`-embedding `L ⟶ M` is obtained
from a fixed one `e` by composing with a power `x ↦ x ^ (#K ^ n)`, `n < [L : K]`, of the
Frobenius of `M`, and these are pairwise distinct
(`FiniteField.bijective_frobeniusAlgHom_pow_comp`).
-/

@[expose] public section

namespace FiniteField

variable (K L : Type*) [Field K] [Fintype K] [Field L] [Algebra K L] [Finite L]
  {M : Type*} [Field M] [Algebra K M]

/-- **The embeddings of a finite field**: for a `K`-embedding `e : L ⟶ M` of a finite extension
`L` of the finite field `K`, the composites of `e` with the powers `Frobⁿ`, `n < [L : K]`, of the
Frobenius of `M` are all the `K`-embeddings `L ⟶ M`, each obtained once. -/
theorem bijective_frobeniusAlgHom_pow_comp (e : L →ₐ[K] M) :
    Function.Bijective fun n : Fin (Module.finrank K L) ↦ (frobeniusAlgHom K M ^ n.1).comp e := by
  refine Function.Injective.bijective_of_nat_card_le (fun i j h ↦ ?_) ?_
  · refine (bijective_frobeniusAlgHom_pow K L).1 (AlgHom.ext fun x ↦ e.injective ?_)
    have := DFunLike.congr_fun h x
    simpa only [AlgHom.comp_apply, AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate,
      map_pow, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using this
  · exact (card_algHom_le_finrank K L M).trans_eq (Nat.card_fin _).symm

end FiniteField
