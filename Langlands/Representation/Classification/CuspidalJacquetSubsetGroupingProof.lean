import Langlands.Representation.Classification.CuspidalJacquetSubsetGroupingStatement
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Fin.Basic

/-! Finite grouping by minimizing the positions of selected original labels. -/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

private theorem group_subset_by_adjacent_swaps {r : ℕ} (S : Finset (Fin r))
    (P : Equiv.Perm (Fin r) → Prop) (hstart : P (Equiv.refl _))
    (hstep : ∀ (e : Equiv.Perm (Fin r)) (j : ℕ) (hj : j + 1 < r),
      e ⟨j, by omega⟩ ∉ S → e ⟨j + 1, hj⟩ ∈ S → P e →
      P ((Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩).trans e)) :
    ∃ e : Equiv.Perm (Fin r), (∀ i : Fin r, i.val < S.card ↔ e i ∈ S) ∧ P e := by
  classical
  let weight (e : Equiv.Perm (Fin r)) : ℕ := ∑ k ∈ S, (e.symm k).val
  obtain ⟨e, he, hmin⟩ := Set.exists_min_image {e | P e} weight
    (Set.toFinite _) ⟨Equiv.refl _, hstart⟩
  have hprev : ∀ (j : ℕ) (hj : j + 1 < r),
      e ⟨j + 1, hj⟩ ∈ S → e ⟨j, by omega⟩ ∈ S := by
    intro j hj hb
    by_contra ha
    let a : Fin r := ⟨j, by omega⟩
    let b : Fin r := ⟨j + 1, hj⟩
    let d := (Equiv.swap a b).trans e
    have hd : P d := hstep e j hj ha hb he
    have hlt : weight d < weight e := by
      apply Finset.sum_lt_sum
      · intro k hk
        have hka : e.symm k ≠ a := by
          intro h
          apply ha
          change e a ∈ S
          rw [← h, Equiv.apply_symm_apply]
          exact hk
        change (Equiv.swap a b (e.symm k)).val ≤ (e.symm k).val
        by_cases hkb : e.symm k = b
        · rw [hkb, Equiv.swap_apply_right]
          exact Nat.le_succ j
        · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]
      · refine ⟨e b, hb, ?_⟩
        change (Equiv.swap a b (e.symm (e b))).val < (e.symm (e b)).val
        rw [e.symm_apply_apply, Equiv.swap_apply_right]
        exact Nat.lt_succ_self j
    exact (not_lt_of_ge (hmin d hd)) hlt
  have hdown : ∀ i j : Fin r, i ≤ j → e j ∈ S → e i ∈ S := by
    cases r with
    | zero => intro i; exact Fin.elim0 i
    | succ r =>
      have hanti : Antitone (fun i : Fin (r + 1) => if e i ∈ S then (1 : ℕ) else 0) := by
        apply Fin.antitone_iff_succ_le.mpr
        intro i
        by_cases hi : e i.castSucc ∈ S
        · simp only [hi, ite_true]
          split_ifs <;> omega
        · have hs : e i.succ ∉ S := fun hs => hi (hprev i.val i.succ.isLt hs)
          simp [hi, hs]
      intro i j hij hj
      have hle := hanti hij
      by_contra hi
      simp [hi, hj] at hle
  let U := S.preimage e e.injective.injOn
  have hcard : U.card = S.card := by
    simp [U, Finset.card_preimage, Set.range_eq_univ.mpr e.surjective]
  refine ⟨e, ?_, he⟩
  intro i
  constructor
  · intro hi
    by_contra hnot
    have hsub : U ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hji
      exact hnot (hdown i j (le_of_not_gt hji) (Finset.mem_preimage.mp hj))
    have hc := Finset.card_le_card hsub
    rw [hcard, Fin.card_Iio] at hc
    omega
  · intro hi
    have hsub : Finset.Iic i ⊆ U := by
      intro j hj
      exact Finset.mem_preimage.mpr (hdown j i (Finset.mem_Iic.mp hj) hi)
    have hc := Finset.card_le_card hsub
    rw [hcard, Fin.card_Iic] at hc
    omega

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Adjacent actual interchange groups a subset while retaining all factors. -/
theorem cuspidalJacquetSubsetGrouping : CuspidalJacquetSubsetGrouping.{uF, uV} F T := by
  classical
  intro hlocal
  let := T.topology
  intro n B π hπ ha hl A hA S hpairs
  let P (e : Equiv.Perm (Fin B.length)) : Prop :=
    SmoothRep.IsSubquotient
      (FiniteTensor.externalSmoothObject (fun i => (A (e i)).obj))
      ((T.normalizedJacquetFunctor (B.permute e)).obj π)
  apply group_subset_by_adjacent_swaps S P hA
  intro e j hj hout hin he
  have hpair := hpairs (e ⟨j, by omega⟩) (e ⟨j + 1, hj⟩) hout hin
  exact hlocal n (B.permute e) π hπ ha hl (fun i => A (e i)) he j hj
    hpair.1 hpair.2

end Langlands.Classification
