import Langlands.LinearAlgebra.RootReflectionCoefficients
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.LinearAlgebra.RootSystem.Base

/-! # Root count bounds for types D5 and F4 -/

noncomputable section

open scoped BigOperators

namespace Langlands.LinearAlgebra

open Langlands.RootReflectionCoefficients

private def d5Positive : Fin 20 → Fin 5 → ℤ :=
  ![![1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0],
    ![0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 1],
    ![1, 1, 0, 0, 0],
    ![0, 1, 1, 0, 0],
    ![0, 0, 1, 1, 0],
    ![0, 0, 1, 0, 1],
    ![1, 1, 1, 0, 0],
    ![0, 1, 1, 1, 0],
    ![0, 1, 1, 0, 1],
    ![0, 0, 1, 1, 1],
    ![1, 1, 1, 1, 0],
    ![1, 1, 1, 0, 1],
    ![0, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1],
    ![0, 1, 2, 1, 1],
    ![1, 1, 2, 1, 1],
    ![1, 2, 2, 1, 1]]

private def d5ReflectionIndex : Fin 5 → Fin 20 → Fin 20 :=
  ![![0, 5, 2, 3, 4, 1, 9, 7, 8, 6, 13, 14, 12, 10, 11, 16, 15, 18, 17, 19],
    ![5, 1, 6, 3, 4, 0, 2, 10, 11, 9, 7, 8, 15, 13, 14, 12, 16, 17, 19, 18],
    ![0, 6, 2, 7, 8, 9, 1, 3, 4, 5, 10, 11, 12, 13, 14, 17, 18, 15, 16, 19],
    ![0, 1, 7, 3, 4, 5, 10, 2, 12, 13, 6, 15, 8, 9, 16, 11, 14, 17, 18, 19],
    ![0, 1, 8, 3, 4, 5, 11, 12, 2, 14, 15, 6, 7, 16, 9, 10, 13, 17, 18, 19]]

private def f4Positive : Fin 24 → Fin 4 → ℤ :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1],
    ![1, 1, 0, 0],
    ![0, 1, 2, 0],
    ![0, 1, 1, 0],
    ![0, 0, 1, 1],
    ![1, 1, 2, 0],
    ![0, 1, 2, 2],
    ![1, 1, 1, 0],
    ![0, 1, 1, 1],
    ![1, 2, 2, 0],
    ![1, 1, 2, 2],
    ![1, 1, 1, 1],
    ![0, 1, 2, 1],
    ![1, 2, 2, 2],
    ![1, 1, 2, 1],
    ![1, 2, 4, 2],
    ![1, 2, 2, 1],
    ![1, 3, 4, 2],
    ![1, 2, 3, 1],
    ![2, 3, 4, 2],
    ![1, 2, 3, 2]]

private def f4Parent : Fin 24 → Fin 24 :=
  ![0, 0, 0, 0, 0, 1, 2, 2, 4, 5, 6, 6, 8, 8, 10, 11, 12, 14, 16, 17, 18, 19, 20, 21]

private def f4ReflectingVertex : Fin 24 → Fin 4 :=
  ![0, 0, 0, 0, 1, 2, 1, 3, 2, 3, 0, 3, 1, 3, 3, 2, 3, 2, 2, 1, 1, 2, 0, 3]

private theorem d5_simple (i : Fin 5) : d5Positive (Fin.castLE (by decide : 5 ≤ 20) i) = Pi.single i 1 := by
  revert i
  decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 400000 in
private theorem d5_reflect (i : Fin 5) (j : Fin 20) :
    reflect (CartanMatrix.D 5) i (d5Positive j) =
      if i.val = j.val then -d5Positive (d5ReflectionIndex i j)
      else d5Positive (d5ReflectionIndex i j) := by
  revert i j
  decide

private theorem f4_simple (i : Fin 4) : f4Positive (Fin.castLE (by decide : 4 ≤ 24) i) = Pi.single i 1 := by
  revert i
  decide

private theorem f4_parent (i : Fin 24) (hi : 4 ≤ i.val) :
    (f4Parent i).val < i.val ∧
      reflect CartanMatrix.F₄ (f4ReflectingVertex i) (f4Positive (f4Parent i)) = f4Positive i := by
  revert i
  decide

private def f4Signed (p : Bool × Fin 24) : Fin 4 → ℤ :=
  if p.1 then f4Positive p.2 else -f4Positive p.2

set_option maxRecDepth 24000 in
set_option maxHeartbeats 1700000 in
private theorem f4Signed_injective : Function.Injective f4Signed := by
  decide

section RootCounts

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (P : RootPairing J ℤ X Y)

/-- A finite reduced based root datum with Cartan matrix D5 has at most forty roots. -/
theorem card_root_le_40_of_typeD5 [Finite J] [P.IsReduced] (b : P.Base) (e : b.support ≃ Fin 5)
    (hD : ∀ i j, P.pairing (e.symm i).val (e.symm j).val = CartanMatrix.D 5 i j) : Nat.card J ≤ 40 := by
  classical
  let a : Fin 5 → J := fun i => (e.symm i).val
  let Signed (x : X) : Prop := ∃ j, x = combination P a (d5Positive j) ∨ x = -combination P a (d5Positive j)
  have hneg {x : X} (hx : Signed x) : Signed (-x) := by
    rcases hx with ⟨j, h | h⟩
    · exact ⟨j, Or.inr (congrArg Neg.neg h)⟩
    · exact ⟨j, Or.inl (by rw [h, neg_neg])⟩
  have hclosed (i : Fin 5) (j : Fin 20) : Signed (P.reflection (a i) (combination P a (d5Positive j))) := by
    have hp : P.coroot' (a i) (combination P a (d5Positive j)) = ∑ k, d5Positive j k * CartanMatrix.D 5 k i := by
      change P.toLinearMap (combination P a (d5Positive j)) (P.coroot (a i)) = _
      simp only [combination, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        RootPairing.root_coroot_eq_pairing, a, hD, smul_eq_mul]
    have hr : P.reflection (a i) (combination P a (d5Positive j)) =
        combination P a (reflect (CartanMatrix.D 5) i (d5Positive j)) := by
      rw [P.reflection_apply, hp]
      simp [combination, reflect, sub_smul, Finset.sum_sub_distrib, ite_smul]
    rw [hr, d5_reflect]
    refine ⟨d5ReflectionIndex i j, ?_⟩
    split
    · right
      simp only [combination, Pi.neg_apply, neg_zsmul, Finset.sum_neg_distrib]
    · exact Or.inl rfl
  have hex (r : J) : Signed (P.root r) := by
    apply b.induction_reflect r (p := fun r => Signed (P.root r))
    · intro i hi
      rw [P.root_reflectionPerm, P.reflection_apply_self]
      exact hneg hi
    · intro i hi
      let j := e ⟨i, hi⟩
      refine ⟨Fin.castLE (by decide : 5 ≤ 20) j, Or.inl ?_⟩
      rw [d5_simple]
      simp [combination, Pi.single_apply, ite_smul, a, j]
    · intro i j hi hj
      let k := e ⟨j, hj⟩
      have hk : a k = j := congrArg Subtype.val (e.symm_apply_apply ⟨j, hj⟩)
      rw [P.root_reflectionPerm, ← hk]
      rcases hi with ⟨l, h | h⟩
      · rw [h]
        exact hclosed k l
      · rw [h, map_neg]
        exact hneg (hclosed k l)
  let v (p : Bool × Fin 20) : X := if p.1 then combination P a (d5Positive p.2) else -combination P a (d5Positive p.2)
  have huv (r : J) : ∃ t, P.root r = v t := by
    rcases hex r with ⟨l, h | h⟩
    · exact ⟨(true, l), h⟩
    · exact ⟨(false, l), h⟩
  choose f hf using huv
  have hcard := Nat.card_le_card_of_injective f (fun _ _ h =>
    P.root.injective ((hf _).trans (h ▸ (hf _).symm)))
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] using hcard

/-- Four independent roots with F4 simple pairings generate at least forty-eight
roots of the ambient integral root datum. -/
theorem card_root_ge_48_of_typeF4 [Finite J] (a : Fin 4 → J)
    (hli : LinearIndependent ℤ (fun j => P.root (a j)))
    (hF : ∀ i j, P.pairing (a i) (a j) = CartanMatrix.F₄ i j) : 48 ≤ Nat.card J := by
  classical
  have hpos (i : Fin 24) : IsRoot P a (f4Positive i) := by
    generalize h : i.val = n
    induction n using Nat.strong_induction_on generalizing i with
    | h n ih =>
      by_cases hi : i.val < 4
      · let j : Fin 4 := ⟨i.val, hi⟩
        have hj : i = Fin.castLE (by decide : 4 ≤ 24) j := rfl
        rw [hj, f4_simple]
        exact isRoot_single P a j
      · obtain ⟨hlt, heq⟩ := f4_parent i (Nat.le_of_not_gt hi)
        rw [← h] at ih
        exact heq ▸ (ih _ hlt (f4Parent i) rfl).reflect P a CartanMatrix.F₄ hF (f4ReflectingVertex i)
  have hex (p : Bool × Fin 24) : IsRoot P a (f4Signed p) := by
    rcases p with ⟨s, i⟩
    obtain ⟨j, hj⟩ := hpos i
    cases s
    · refine ⟨P.reflectionPerm j j, ?_⟩
      rw [P.root_reflectionPerm, P.reflection_apply_self, hj]
      simp only [f4Signed, Bool.false_eq_true, ite_false, combination, Pi.neg_apply, neg_zsmul,
        Finset.sum_neg_distrib]
    · exact ⟨j, hj⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro x y hxy
    have he := (hf x).symm.trans ((congrArg P.root hxy).trans (hf y))
    apply f4Signed_injective
    funext i
    exact Fintype.linearIndependent_iffₛ.mp hli _ _ he i
  have hcard := Nat.card_le_card_of_injective f hinj
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] using hcard

end RootCounts

/-- Root count bounds for D5 and for a subsystem with an independent F4 base. -/
def CartanD5F4RootCountsStatement : Prop :=
  ∀ (J X Y : Type*) [AddCommGroup X] [AddCommGroup Y] (P : RootPairing J ℤ X Y) [Finite J],
    (∀ [P.IsReduced] (b : P.Base) (e : b.support ≃ Fin 5),
      (∀ i j, P.pairing (e.symm i).val (e.symm j).val = CartanMatrix.D 5 i j) → Nat.card J ≤ 40) ∧
    (∀ a : Fin 4 → J, LinearIndependent ℤ (fun j => P.root (a j)) →
      (∀ i j, P.pairing (a i) (a j) = CartanMatrix.F₄ i j) → 48 ≤ Nat.card J)

theorem cartanD5F4RootCounts : CartanD5F4RootCountsStatement := by
  intro J X Y _ _ P _
  refine ⟨?_, card_root_ge_48_of_typeF4 P⟩
  intro _ b e h
  exact card_root_le_40_of_typeD5 P b e h

end Langlands.LinearAlgebra
