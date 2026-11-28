import Langlands.LinearAlgebra.RootReflectionCoefficients
import Langlands.LinearAlgebra.SimplyConnectedCartanComponents
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.Data.Fintype.Sigma

/-! # Root counts for small products of type A components -/

noncomputable section

open scoped BigOperators

namespace Langlands.LinearAlgebra

open Langlands.RootReflectionCoefficients SimplyConnectedCartanComponents

private def ChainIndex (n : ℕ) := {p : Fin (n + 1) × Fin (n + 1) // p.1 ≠ p.2}

private instance (n : ℕ) : Fintype (ChainIndex n) := inferInstanceAs
  (Fintype {p : Fin (n + 1) × Fin (n + 1) // p.1 ≠ p.2})

private def chain {n : ℕ} (p : ChainIndex n) (i : Fin n) : ℤ :=
  (if p.val.1.val ≤ i.val ∧ i.val < p.val.2.val then 1 else 0) -
    (if p.val.2.val ≤ i.val ∧ i.val < p.val.1.val then 1 else 0)

private def reverseChain {n : ℕ} (p : ChainIndex n) : ChainIndex n :=
  ⟨(p.val.2, p.val.1), p.property.symm⟩

private theorem chain_reverse {n : ℕ} (p : ChainIndex n) : chain (reverseChain p) = -chain p := by
  funext i
  simp only [chain, reverseChain, Pi.neg_apply, neg_sub]
  rfl

private def simpleChain {n : ℕ} (i : Fin n) : ChainIndex n :=
  ⟨(i.castSucc, i.succ), by intro h; have := congrArg Fin.val h; simp at this⟩

private theorem chain_simple {n : ℕ} (i : Fin n) : chain (simpleChain i) = Pi.single i 1 := by
  funext j
  have h : i.val ≤ j.val ∧ j.val < i.val + 1 ↔ j = i := by
    rw [Fin.ext_iff]
    omega
  have h' : ¬ (i.val + 1 ≤ j.val ∧ j.val < i.val) := by omega
  simp only [chain, simpleChain, Fin.val_castSucc, Fin.val_succ, h, h', ite_false, sub_zero,
    Pi.single_apply]

private def ReflectionClosed (n : ℕ) : Prop :=
  ∀ (i : Fin n) (p : ChainIndex n), ∃ q : ChainIndex n,
    reflect (CartanMatrix.A n) i (chain p) = chain q

private instance (n : ℕ) : Decidable (ReflectionClosed n) :=
  inferInstanceAs (Decidable (∀ (i : Fin n) (p : ChainIndex n), ∃ q : ChainIndex n,
    reflect (CartanMatrix.A n) i (chain p) = chain q))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
private theorem reflectionClosed_of_le_four (n : ℕ) (hn : n ≤ 4) : ReflectionClosed n := by
  interval_cases n <;> decide

private theorem card_chainIndex (n : ℕ) : Fintype.card (ChainIndex n) = n * (n + 1) := by
  let e : ChainIndex n ≃ (Σ a : Fin (n + 1), {b : Fin (n + 1) // b ≠ a}) :=
    { toFun := fun p => ⟨p.val.1, p.val.2, p.property.symm⟩
      invFun := fun p => ⟨(p.1, p.2.val), p.2.property.symm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  have h (a : Fin (n + 1)) : Fintype.card {b : Fin (n + 1) // b ≠ a} = n := by
    rw [Fintype.card_subtype_compl (· = a), Fintype.card_subtype_eq, Fintype.card_fin]
    omega
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
  rfl

private theorem sum_rank_mul_succ_le_22 {C : Type*} [Fintype C]
    (n : C → ℕ) (hn : ∀ c, n c ≤ 4) (ht : ∑ c, n c ≤ 5) :
    ∑ c, n c * (n c + 1) ≤ 22 := by
  classical
  by_cases hs : ∀ c, n c ≤ 3
  · calc
      (∑ c, n c * (n c + 1)) ≤ ∑ c, n c * 4 :=
        Finset.sum_le_sum fun c _ => Nat.mul_le_mul_left _ (by have := hs c; omega)
      _ ≤ 22 := by rw [← Finset.sum_mul]; omega
  · push Not at hs
    obtain ⟨c, hc⟩ := hs
    have h4 : n c = 4 := by have := hn c; omega
    let s := (Finset.univ : Finset C).erase c
    have ht' := Finset.sum_erase_add (Finset.univ : Finset C) n (Finset.mem_univ c)
    have hs' : ∑ b ∈ s, n b ≤ 1 := by change ∑ b ∈ s, n b + n c = _ at ht'; omega
    have hrest : (∑ b ∈ s, n b * (n b + 1)) ≤ 2 := by
      calc
        (∑ b ∈ s, n b * (n b + 1)) ≤ ∑ b ∈ s, n b * 2 := by
          apply Finset.sum_le_sum
          intro b hb
          have hb' : n b ≤ ∑ i ∈ s, n i := Finset.single_le_sum (fun i _ => Nat.zero_le _) hb
          exact Nat.mul_le_mul_left _ (by omega)
        _ ≤ 2 := by rw [← Finset.sum_mul]; omega
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c), h4]
    change (∑ b ∈ s, n b * (n b + 1)) + 4 * (4 + 1) ≤ 22
    omega

section RootCount

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootPairing J ℤ X Y) [Finite J] [P.IsReduced] (b : P.Base)

/-- If each Cartan component of a reduced based datum is type A of rank at
most four, the total rank bound five gives at most twenty-two roots. -/
theorem card_root_le_22_of_small_typeA_components
    (hrank : Nat.card b.support ≤ 5)
    (hA : ∀ c : Component b, ∃ (n : ℕ) (_ : n ≤ 4)
      (e : {j : b.support // component b j = c} ≃ Fin n),
        ∀ i j, P.pairing (e.symm i).val.val (e.symm j).val.val = CartanMatrix.A n i j) :
    Nat.card J ≤ 22 := by
  classical
  choose n hn e he using hA
  let : Fintype (Component b) := Fintype.ofFinite _
  let a (c : Component b) (i : Fin (n c)) : b.support := (e c).symm i
  have ha (c : Component b) (i : Fin (n c)) : component b (a c i) = c := ((e c).symm i).property
  let V := Σ c : Component b, ChainIndex (n c)
  let value (p : V) : X := combination P (fun i => (a p.1 i).val) (chain p.2)
  have hex (r : J) : ∃ p : V, P.root r = value p := by
    apply b.induction_reflect r (p := fun r => ∃ p : V, P.root r = value p)
    · rintro i ⟨⟨c, p⟩, hp⟩
      refine ⟨⟨c, reverseChain p⟩, ?_⟩
      rw [P.root_reflectionPerm, P.reflection_apply_self, hp]
      simp only [value, chain_reverse, combination, Pi.neg_apply, neg_zsmul, Finset.sum_neg_distrib]
    · intro i hi
      let v : b.support := ⟨i, hi⟩
      let c := component b v
      let j := e c ⟨v, rfl⟩
      have hj : a c j = v := congrArg Subtype.val ((e c).symm_apply_apply ⟨v, rfl⟩)
      refine ⟨⟨c, simpleChain j⟩, ?_⟩
      simp [value, chain_simple, combination, Pi.single_apply, ite_smul, hj, v]
    · rintro i j ⟨⟨c, p⟩, hp⟩ hj
      let v : b.support := ⟨j, hj⟩
      rw [P.root_reflectionPerm, hp]
      by_cases hs : component b v = c
      · let l := e c ⟨v, hs⟩
        have hl : (a c l).val = j := congrArg (fun x => x.val.val) ((e c).symm_apply_apply ⟨v, hs⟩)
        obtain ⟨q, hq⟩ := reflectionClosed_of_le_four (n c) (hn c) l p
        refine ⟨⟨c, q⟩, ?_⟩
        change P.reflection j (combination P (fun k => (a c k).val) (chain p)) =
          combination P (fun k => (a c k).val) (chain q)
        rw [← hq, ← hl]
        have hpair : P.coroot' (a c l).val (combination P (fun k => (a c k).val) (chain p)) =
            ∑ k, chain p k * CartanMatrix.A (n c) k l := by
          change P.toLinearMap (combination P _ (chain p)) (P.coroot (a c l).val) = _
          simp only [combination, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
            RootPairing.root_coroot_eq_pairing, a, he, smul_eq_mul]
        rw [P.reflection_apply, hpair]
        simp [combination, reflect, sub_smul, Finset.sum_sub_distrib, ite_smul]
      · refine ⟨⟨c, p⟩, ?_⟩
        have hpair (k : Fin (n c)) : P.pairing (a c k).val j = 0 :=
          pairing_eq_zero_of_component_ne b (a c k) v (by rw [ha]; exact Ne.symm hs)
        have hz : P.coroot' j (value ⟨c, p⟩) = 0 := by
          change P.toLinearMap (combination P (fun k => (a c k).val) (chain p)) (P.coroot j) = _
          simp [combination, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
            RootPairing.root_coroot_eq_pairing, hpair]
        rw [P.reflection_apply, hz, zero_smul, sub_zero]
  choose f hf using hex
  have hfin : Nat.card J ≤ Nat.card V := Nat.card_le_card_of_injective f (fun _ _ h =>
    P.root.injective ((hf _).trans (h ▸ (hf _).symm)))
  have hrank' : ∑ c, n c ≤ 5 := by
    have hh := Nat.card_congr ((Equiv.sigmaFiberEquiv (component b)).symm.trans
      (Equiv.sigmaCongrRight e))
    rw [hh, Nat.card_eq_fintype_card, Fintype.card_sigma] at hrank
    simpa only [Fintype.card_fin] using hrank
  apply hfin.trans
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [card_chainIndex]
  exact sum_rank_mul_succ_le_22 n hn hrank'

end RootCount

/-- Products of type A of total rank at most five, each component of rank at
most four, have at most twenty-two roots. -/
def SmallTypeAComponentRootBoundStatement : Prop :=
  ∀ (J X Y : Type*) [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing J ℤ X Y) [Finite J] [P.IsReduced] (b : P.Base),
    Nat.card b.support ≤ 5 →
    (∀ c : Component b, ∃ (n : ℕ) (_ : n ≤ 4) (e : {j : b.support // component b j = c} ≃ Fin n),
      ∀ i j, P.pairing (e.symm i).val.val (e.symm j).val.val = CartanMatrix.A n i j) → Nat.card J ≤ 22

theorem smallTypeAComponentRootBound : SmallTypeAComponentRootBoundStatement := by
  intro J X Y _ _ P _ _ b hrank hA
  exact card_root_le_22_of_small_typeA_components P b hrank hA

end Langlands.LinearAlgebra
