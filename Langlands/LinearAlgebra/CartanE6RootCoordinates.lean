import Langlands.LinearAlgebra.CartanE6Root
import Mathlib.LinearAlgebra.RootSystem.Base

/-! # Integral coordinates of the roots of type E6 -/

noncomputable section

namespace Langlands.CartanE6Root

open RootReflectionCoefficients
open scoped BigOperators

/-- The positive roots in the basis and numbering of `CartanMatrix.E 6`.
The simple roots are the first six entries. -/
def positiveCoefficients : Fin 36 → (Fin 6 → ℤ) :=
  ![![1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1],
    ![1, 0, 1, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0],
    ![0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 1, 1],
    ![1, 0, 1, 1, 0, 0],
    ![0, 1, 1, 1, 0, 0],
    ![0, 1, 0, 1, 1, 0],
    ![0, 0, 1, 1, 1, 0],
    ![0, 0, 0, 1, 1, 1],
    ![1, 1, 1, 1, 0, 0],
    ![1, 0, 1, 1, 1, 0],
    ![0, 1, 1, 1, 1, 0],
    ![0, 1, 0, 1, 1, 1],
    ![0, 0, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 0],
    ![1, 0, 1, 1, 1, 1],
    ![0, 1, 1, 2, 1, 0],
    ![0, 1, 1, 1, 1, 1],
    ![1, 1, 1, 2, 1, 0],
    ![1, 1, 1, 1, 1, 1],
    ![0, 1, 1, 2, 1, 1],
    ![1, 1, 2, 2, 1, 0],
    ![1, 1, 1, 2, 1, 1],
    ![0, 1, 1, 2, 2, 1],
    ![1, 1, 2, 2, 1, 1],
    ![1, 1, 1, 2, 2, 1],
    ![1, 1, 2, 2, 2, 1],
    ![1, 1, 2, 3, 2, 1],
    ![1, 2, 2, 3, 2, 1]]

private def parent : Fin 36 → Fin 36 :=
  ![0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 6, 7, 7, 8, 9, 11, 11, 12, 13, 14, 16, 17, 18, 18, 21, 21, 23, 25, 25, 27, 28, 29, 31, 33, 34]

private def reflectingVertex : Fin 36 → Fin 6 :=
  ![0, 0, 0, 0, 0, 0, 2, 3, 3, 4, 5, 3, 2, 4, 4, 5, 1, 4, 4, 5, 5, 4, 5, 3, 5, 3, 5, 5, 2, 5, 4, 5, 4, 4, 3, 1]

private def reflectionIndex : Fin 6 → Fin 36 → Fin 36 :=
  ![![0, 1, 6, 3, 4, 5, 2, 7, 11, 9, 10, 8, 16, 13, 17, 15, 12, 14, 21, 19, 22, 18, 20, 25, 26, 23, 24, 29, 28, 27, 32, 31, 30, 33, 34, 35],
    ![0, 1, 2, 7, 4, 5, 6, 3, 12, 13, 10, 16, 8, 9, 18, 19, 11, 21, 14, 15, 24, 17, 26, 23, 20, 25, 22, 27, 28, 29, 30, 31, 32, 33, 35, 34],
    ![6, 1, 2, 8, 4, 5, 0, 12, 3, 14, 10, 11, 7, 18, 9, 20, 16, 17, 13, 24, 15, 21, 22, 23, 19, 28, 26, 27, 25, 31, 30, 29, 33, 32, 34, 35],
    ![0, 7, 8, 3, 9, 5, 11, 1, 2, 4, 15, 6, 12, 13, 14, 10, 16, 17, 23, 19, 20, 25, 22, 18, 27, 21, 29, 24, 28, 26, 30, 31, 32, 34, 33, 35],
    ![0, 1, 2, 9, 4, 10, 6, 13, 14, 3, 5, 17, 18, 7, 8, 15, 21, 11, 12, 19, 20, 16, 22, 23, 24, 25, 26, 30, 28, 32, 27, 33, 29, 31, 34, 35],
    ![0, 1, 2, 3, 10, 5, 6, 7, 8, 15, 4, 11, 12, 19, 20, 9, 16, 22, 24, 13, 14, 26, 17, 27, 18, 29, 21, 23, 31, 25, 30, 28, 32, 33, 34, 35]]

private theorem simpleCoefficients (i : Fin 6) :
    positiveCoefficients (Fin.castLE (by decide : 6 ≤ 36) i) = Pi.single i 1 := by
  revert i
  decide

private theorem parent_spec (i : Fin 36) (hi : 6 ≤ i.val) :
    (parent i).val < i.val ∧
      reflect (CartanMatrix.E 6) (reflectingVertex i) (positiveCoefficients (parent i)) =
        positiveCoefficients i := by
  revert i
  decide

set_option maxHeartbeats 900000 in
private theorem reflectionIndex_spec (j : Fin 6) (i : Fin 36) :
    reflect (CartanMatrix.E 6) j (positiveCoefficients i) =
      if j.val = i.val then -positiveCoefficients (reflectionIndex j i)
      else positiveCoefficients (reflectionIndex j i) := by
  revert j i
  decide

section RootDatum

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (a : Fin 6 → J)

/-- Each listed vector is the integral expression of a root of the supplied datum. -/
theorem isRoot_positiveCoefficients
    (hM : ∀ i j, P.pairing (a i) (a j) = CartanMatrix.E 6 i j) (i : Fin 36) :
    IsRoot P a (positiveCoefficients i) := by
  generalize h : i.val = n
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    by_cases hi : i.val < 6
    · let j : Fin 6 := ⟨i.val, hi⟩
      have hj : i = Fin.castLE (by decide : 6 ≤ 36) j := rfl
      rw [hj, simpleCoefficients]
      exact isRoot_single P a j
    · obtain ⟨hlt, heq⟩ := parent_spec i (Nat.le_of_not_gt hi)
      rw [← h] at ih
      exact heq ▸ (ih _ hlt (parent i) rfl).reflect P a (CartanMatrix.E 6) hM (reflectingVertex i)

/-- The signed coefficient list exhausts the actual roots of every based datum
with the given reduced E6 Cartan matrix. -/
theorem exists_signedCoefficients [Finite J] [P.IsReduced] (b : P.Base)
    (e : b.support ≃ Fin 6)
    (hM : ∀ i j, P.pairing (e.symm i).val (e.symm j).val = CartanMatrix.E 6 i j) (r : J) :
    let a : Fin 6 → J := fun j => (e.symm j).val
    ∃ i : Fin 36, P.root r = combination P a (positiveCoefficients i) ∨
      P.root r = -combination P a (positiveCoefficients i) := by
  classical
  let a : Fin 6 → J := fun j => (e.symm j).val
  let signed (x : X) : Prop := ∃ i : Fin 36,
    x = combination P a (positiveCoefficients i) ∨ x = -combination P a (positiveCoefficients i)
  change signed (P.root r)
  have hneg {x : X} (hx : signed x) : signed (-x) := by
    obtain ⟨i, h | h⟩ := hx
    · exact ⟨i, Or.inr (congrArg Neg.neg h)⟩
    · exact ⟨i, Or.inl (by rw [h, neg_neg])⟩
  have hreflect (j : Fin 6) (c : Fin 6 → ℤ) :
      P.reflection (a j) (combination P a c) =
        combination P a (reflect (CartanMatrix.E 6) j c) := by
    have hp : P.coroot' (a j) (combination P a c) = ∑ k, c k * CartanMatrix.E 6 k j := by
      change P.toLinearMap (combination P a c) (P.coroot (a j)) = _
      simp only [combination, map_sum, map_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, RootPairing.root_coroot_eq_pairing, a, hM, smul_eq_mul]
    rw [P.reflection_apply, hp]
    simp [combination, reflect, sub_smul, Finset.sum_sub_distrib, ite_smul]
  have hstable (j : Fin 6) (i : Fin 36) :
      signed (P.reflection (a j) (combination P a (positiveCoefficients i))) := by
    rw [hreflect, reflectionIndex_spec]
    refine ⟨reflectionIndex j i, ?_⟩
    split
    · right
      simp only [combination, Pi.neg_apply, neg_zsmul, Finset.sum_neg_distrib]
    · exact Or.inl rfl
  apply b.induction_reflect r (p := fun r => signed (P.root r))
  · intro j hj
    rw [P.root_reflectionPerm, P.reflection_apply_self]
    exact hneg hj
  · intro j hj
    let i := e ⟨j, hj⟩
    refine ⟨Fin.castLE (by decide : 6 ≤ 36) i, Or.inl ?_⟩
    rw [simpleCoefficients]
    simp [combination, Pi.single_apply, ite_smul, a, i]
  · intro j l hj hl
    let k := e ⟨l, hl⟩
    have hk : a k = l := congrArg Subtype.val (e.symm_apply_apply ⟨l, hl⟩)
    rw [P.root_reflectionPerm, ← hk]
    obtain ⟨i, h | h⟩ := hj
    · rw [h]
      exact hstable k i
    · rw [h, map_neg]
      exact hneg (hstable k i)

end RootDatum

end Langlands.CartanE6Root
