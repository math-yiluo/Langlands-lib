import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Multiset.Filter
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Rearrangement and the weights of a product of minors -/

noncomputable section

open Finset

open scoped BigOperators

set_option autoImplicit false

namespace Langlands.Archimedean.RealMinorWeightBound

variable {ι κ : Type*} [Fintype ι]

/-- Equal multisets of values of two finite families admit a matching permutation. -/
theorem exists_perm_of_multiset_eq {f g : ι → κ}
    (h : (univ : Finset ι).val.map f = (univ : Finset ι).val.map g) :
    ∃ p : Equiv.Perm ι, ∀ i, g (p i) = f i := by
  classical
  have hcard (u : ι → κ) (z : κ) :
      Fintype.card {i // u i = z} = ((univ : Finset ι).val.map u).count z := by
    rw [Fintype.card_subtype, Multiset.count_map, ← Finset.filter_val]
    simp only [Finset.card, eq_comm (a := z)]
  let e (z : κ) : {i // f i = z} ≃ {i // g i = z} :=
    Fintype.equivOfCardEq (by rw [hcard, hcard, h])
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

private theorem sum_mul_le_of_antivary_on_fibers (c : ι → κ) (x l : ι → ℝ)
    (p : Equiv.Perm ι) (hp : ∀ i, c (p i) = c i)
    (hord : ∀ i j, c i = c j → x i < x j → l j ≤ l i) :
    ∑ i, l i * x i ≤ ∑ i, l i * x (p i) := by
  classical
  have hm : ∀ i ∈ (univ : Finset ι), c i ∈ univ.image c :=
    fun _ => mem_image_of_mem c
  rw [← sum_fiberwise_of_maps_to hm (fun i => l i * x i),
    ← sum_fiberwise_of_maps_to hm (fun i => l i * x (p i))]
  refine sum_le_sum fun z _ => ?_
  let q : Equiv.Perm {i // c i = z} :=
    p.subtypeEquiv fun i => by rw [hp]
  have hanti : Antivary (fun i : {i // c i = z} => l i) (fun i => x i) :=
    fun i j hij => hord i j (i.property.trans j.property.symm) hij
  have hsub (f : ι → ℝ) :
      (∑ i ∈ univ.filter (fun i => c i = z), f i) = ∑ i : {i // c i = z}, f i :=
    sum_subtype (p := fun i => c i = z) _ (by simp) f
  rw [hsub, hsub]
  exact hanti.sum_mul_le_sum_mul_comp_perm (σ := q)

/-- Rearrangement on the fibers forces a shift of bounded squared norm to be zero. -/
theorem eq_of_energy_le_of_antivary (c : ι → κ) (x l m : ι → ℝ)
    (p : Equiv.Perm ι) (hp : ∀ i, c (p i) = c i)
    (hord : ∀ i j, c i = c j → x i < x j → l j ≤ l i)
    (hm : ∀ i, m i = l i + (x (p i) - x i))
    (hbound : ∑ i, m i ^ 2 ≤ ∑ i, l i ^ 2) :
    ∀ i, x (p i) = x i ∧ m i = l i := by
  let δ i := x (p i) - x i
  have hcross : 0 ≤ ∑ i, l i * δ i := by
    simpa only [δ, mul_sub, sum_sub_distrib, sub_nonneg] using
      sum_mul_le_of_antivary_on_fibers c x l p hp hord
  have hexpand :
      (∑ i, m i ^ 2) = (∑ i, l i ^ 2) + 2 * (∑ i, l i * δ i) + ∑ i, δ i ^ 2 := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [hm]
    dsimp only [δ]
    ring
  have hnonneg : 0 ≤ ∑ i, δ i ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hzero : ∑ i, δ i ^ 2 = 0 := by linarith
  intro i
  have hi := (sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (δ j))).mp hzero i
    (mem_univ i)
  have hδ : δ i = 0 := by nlinarith
  have hi' : x (p i) - x i = 0 := hδ
  exact ⟨sub_eq_zero.mp hi', by rw [hm, hi', add_zero]⟩

section Families

variable {r : Type*} [Fintype r] [DecidableEq ι]

/-- The weight at a position is the number of column sets containing it. -/
def weight (S : r → Finset ι) (i : ι) : ℕ :=
  (univ.filter fun s => i ∈ S s).card

omit [Fintype ι] in
theorem weight_eq_sum (S : r → Finset ι) (i : ι) :
    weight S i = ∑ s, if i ∈ S s then 1 else 0 := by
  rw [weight, card_eq_sum_ones, sum_filter]

private theorem energy_eq_intersection_sum (S : r → Finset ι) :
    (∑ i, weight S i ^ 2) = ∑ s, ∑ t, (S s ∩ S t).card := by
  simp only [weight_eq_sum, pow_two]
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  have hfilter : univ.filter (· ∈ S s ∩ S t) = S s ∩ S t := by ext i; simp
  rw [← hfilter, card_eq_sum_ones, sum_filter]
  refine sum_congr rfl fun i _ => ?_
  by_cases hs : i ∈ S s <;> by_cases ht : i ∈ S t <;> simp [hs, ht]

/-- A family is nested by size when the smaller set in every pair is a subset of the larger. -/
def Nested (S : r → Finset ι) : Prop :=
  ∀ s t, (S s).card ≤ (S t).card → S s ⊆ S t

/-- Among families of the same sizes, nested families maximize the sum of squared weights.
Equality forces nesting. -/
theorem energy_le_and_nested_of_eq (S R : r → Finset ι) (hcard : ∀ s, (S s).card = (R s).card)
    (hR : Nested R) :
    (∑ i, weight S i ^ 2) ≤ ∑ i, weight R i ^ 2 ∧
      ((∑ i, weight S i ^ 2) = ∑ i, weight R i ^ 2 → Nested S) := by
  rw [energy_eq_intersection_sum, energy_eq_intersection_sum]
  have hterm (s t : r) : (S s ∩ S t).card ≤ (R s ∩ R t).card := by
    rcases le_total (R s).card (R t).card with h | h
    · rw [inter_eq_left.mpr (hR s t h), ← hcard s]
      exact card_le_card inter_subset_left
    · rw [inter_eq_right.mpr (hR t s h), ← hcard t]
      exact card_le_card inter_subset_right
  have hsum (s : r) : (∑ t, (S s ∩ S t).card) ≤ ∑ t, (R s ∩ R t).card :=
    sum_le_sum fun t _ => hterm s t
  refine ⟨sum_le_sum fun s _ => hsum s, fun heq s t hst => ?_⟩
  have hs := (sum_eq_sum_iff_of_le fun j _ => hsum j).mp heq s (mem_univ s)
  have ht := (sum_eq_sum_iff_of_le fun j _ => hterm s j).mp hs t (mem_univ t)
  have hRst : (R s).card ≤ (R t).card := by simpa only [← hcard] using hst
  rw [inter_eq_left.mpr (hR s t hRst), ← hcard s] at ht
  exact inter_eq_left.mp (eq_of_subset_of_card_le inter_subset_left ht.ge)

omit [Fintype ι] in
/-- A nested family is determined by its sizes and weights. -/
theorem eq_of_nested_of_weight_eq {S R : r → Finset ι}
    (hS : Nested S) (hR : Nested R) (hcard : ∀ s, (S s).card = (R s).card)
    (hweight : ∀ i, weight S i = weight R i) : S = R := by
  classical
  have heq (i : ι) : (univ.filter fun s => i ∈ S s) = (univ.filter fun s => i ∈ R s) := by
    have hcomp : (univ.filter fun s => i ∈ S s) ⊆ (univ.filter fun s => i ∈ R s) ∨
        (univ.filter fun s => i ∈ R s) ⊆ (univ.filter fun s => i ∈ S s) := by
      by_contra! h
      obtain ⟨s, hsS, hsR⟩ := not_subset.mp h.1
      obtain ⟨t, htR, htS⟩ := not_subset.mp h.2
      simp only [mem_filter, mem_univ, true_and] at hsS hsR htS htR
      rcases le_total (S s).card (S t).card with hst | hts
      · exact htS (hS s t hst hsS)
      · exact hsR (hR t s (by simpa only [← hcard] using hts) htR)
    rcases hcomp with h | h
    · exact eq_of_subset_of_card_le h (hweight i).ge
    · exact (eq_of_subset_of_card_le h (hweight i).le).symm
  funext s
  ext i
  simpa only [mem_filter, mem_univ, true_and] using
    Iff.of_eq (congrArg (fun T : Finset r => s ∈ T) (heq i))

end Families

end Langlands.Archimedean.RealMinorWeightBound
