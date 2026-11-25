/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.GroupTheory.Index

/-!

# Sums over coset representatives

For subgroups `U ≤ V` of finite index in a group `G` and a function `f` on `G` which is invariant
under right multiplication by `V`, the sum of `f` over representatives of `G ⧸ U` is the relative
index `[V : U]` times the sum over representatives of `G ⧸ V`
(`Subgroup.sum_quotient_out_eq_relIndex_nsmul`).

-/

@[expose] public section

namespace Subgroup

variable {G : Type*} [Group G] {A : Type*} [AddCommMonoid A]

/-- **Sums over coset representatives**: if `U ≤ V` and `f` is invariant under right
multiplication by `V`, the sum of `f` over representatives of `G ⧸ U` is `[V : U]` times the sum
over representatives of `G ⧸ V`. -/
lemma sum_quotient_out_eq_relIndex_nsmul {U V : Subgroup G} (hUV : U ≤ V) [Fintype (G ⧸ U)]
    [Fintype (G ⧸ V)] (f : G → A) (hf : ∀ g, ∀ v ∈ V, f (g * v) = f g) :
    ∑ q : G ⧸ U, f q.out = U.relIndex V • ∑ q : G ⧸ V, f q.out := by
  classical
  have hF : ∀ g : G, f g = f (QuotientGroup.mk (s := V) g).out := by
    intro g
    obtain ⟨v, hv, e⟩ : ∃ v ∈ V, (QuotientGroup.mk (s := V) g).out = g * v := by
      refine ⟨g⁻¹ * (QuotientGroup.mk (s := V) g).out, ?_, (mul_inv_cancel_left g _).symm⟩
      exact QuotientGroup.eq.mp (QuotientGroup.out_eq' (g : G ⧸ V)).symm
    rw [e, hf g v hv]
  have : Finite (V ⧸ U.subgroupOf V) := by
    have := Finite.of_fintype (G ⧸ U)
    have := Finite.of_equiv _ (quotientEquivProdOfLE hUV)
    exact Finite.of_injective (fun b ↦ ((QuotientGroup.mk 1 : G ⧸ V), b))
      (fun _ _ h ↦ (Prod.ext_iff.mp h).2)
  let := Fintype.ofFinite (V ⧸ U.subgroupOf V)
  calc ∑ q : G ⧸ U, f q.out
      = ∑ q : G ⧸ U, f (quotientEquivProdOfLE hUV q).1.out := by
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        rw [hF q.out]
        congr 2
        conv_rhs => rw [← Quotient.out_eq' q]
        rfl
    _ = ∑ p : (G ⧸ V) × (V ⧸ U.subgroupOf V), f p.1.out :=
        Fintype.sum_equiv (quotientEquivProdOfLE hUV) _ _ fun _ ↦ rfl
    _ = U.relIndex V • ∑ q : G ⧸ V, f q.out := by
        rw [Fintype.sum_prod_type, ← Finset.sum_nsmul]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        simp only [Finset.sum_const, Finset.card_univ, relIndex, index, Nat.card_eq_fintype_card]

/-- **Averages over a smaller subgroup**: if `U ≤ V`, `f` is invariant under right multiplication
by `V` and `[G : V] • a` is the sum of `f` over representatives of `G ⧸ V`, then `[G : U] • a` is
the sum of `f` over representatives of `G ⧸ U`, indexed by `Fin [G : U]`. -/
lemma card_nsmul_eq_sum_fin_of_le {U V : Subgroup G} (hUV : U ≤ V) [Fintype (G ⧸ U)]
    [Fintype (G ⧸ V)] (f : G → A) (hf : ∀ g, ∀ v ∈ V, f (g * v) = f g) (a : A)
    (ha : Fintype.card (G ⧸ V) • a = ∑ q : G ⧸ V, f q.out) :
    Fintype.card (G ⧸ U) • a =
      ∑ i : Fin (Fintype.card (G ⧸ U)), f ((Fintype.equivFin (G ⧸ U)).symm i).out := by
  rw [Equiv.sum_comp (Fintype.equivFin (G ⧸ U)).symm (fun q ↦ f q.out),
    sum_quotient_out_eq_relIndex_nsmul hUV f hf, ← ha, smul_smul,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← index, ← index,
    relIndex_mul_index hUV]

end Subgroup
