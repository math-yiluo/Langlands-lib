import Langlands.Representation.Archimedean.ComplexStandardHomExponent
import Langlands.Representation.Archimedean.ComplexStandardHomTranspose
import Langlands.Representation.Archimedean.ComplexLanglandsQuotientUniqueReduction

/-!
# Intertwinings from a Langlands-ordered standard module to an opposite-ordered one

`ComplexStandardOppositeOrderHomStatement` (a nonzero intertwining map from the standard module
of a Langlands-ordered list `ds` to the standard module of a list `cs` with non-decreasing real
exponents forces `ds.Perm cs`) is reduced to two statements about intertwinings between complex
principal series:

* `ComplexStandardHomExponentStatement` (E): the exponents of the target are a permutation of
  those of the source shifted by nonnegative integer combinations of simple roots, separately in
  the holomorphic and antiholomorphic coordinates;
* `ComplexStandardHomTransposeStatement` (TP): a nonzero intertwining map `X(d) → X(c)` gives a
  nonzero intertwining map `X(c⁻¹) → X(d⁻¹)` (contragredient duality).

The reduction is a prefix-sum (dominance order) argument.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

/-- `E` and `TP` imply `ComplexStandardOppositeOrderHomStatement`. -/
def ComplexStandardOppositeOrderHomReductionStatement : Prop :=
  ComplexStandardHomExponentStatement → ComplexStandardHomTransposeStatement →
    ComplexStandardOppositeOrderHomStatement

section Combinatorics

/-- The indices `j : Fin n` with `j < k`. -/
abbrev finPrefix (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => (j : ℕ) < k)

theorem card_finPrefix {n k : ℕ} (hk : k ≤ n) : (finPrefix n k).card = k := by
  simp only [finPrefix, Fin.card_filter_val_lt]
  omega

theorem finPrefix_succ {n : ℕ} (j : Fin n) :
    finPrefix n ((j : ℕ) + 1) = insert j (finPrefix n j) := by
  ext i
  simp only [finPrefix, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.ext_iff]
  omega

/-- For an antitone `x`, the sum over any `k`-element set is at most the sum of the first `k`
values. -/
theorem sum_le_sum_finPrefix_of_antitone {n : ℕ} {x : Fin n → ℝ} (hx : Antitone x)
    (s : Finset (Fin n)) : ∑ j ∈ s, x j ≤ ∑ j ∈ finPrefix n s.card, x j := by
  have hsn : s.card ≤ n := by simpa using s.card_le_univ
  have hP := card_finPrefix hsn
  rw [← Finset.sum_sdiff_le_sum_sdiff]
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · rw [Finset.card_eq_zero.mp h0]
    simp [finPrefix]
  · let m : Fin n := ⟨s.card - 1, by omega⟩
    have hcard : (s \ finPrefix n s.card).card = (finPrefix n s.card \ s).card :=
      Finset.card_sdiff_comm hP.symm
    calc ∑ j ∈ s \ finPrefix n s.card, x j ≤ (s \ finPrefix n s.card).card • x m := by
          apply Finset.sum_le_card_nsmul
          intro j hj
          simp only [Finset.mem_sdiff, finPrefix, Finset.mem_filter, Finset.mem_univ,
            true_and, not_lt] at hj
          exact hx (Fin.le_def.mpr (by simp only [m]; omega))
      _ = (finPrefix n s.card \ s).card • x m := by rw [hcard]
      _ ≤ ∑ j ∈ finPrefix n s.card \ s, x j := by
          apply Finset.card_nsmul_le_sum
          intro j hj
          simp only [Finset.mem_sdiff, finPrefix, Finset.mem_filter, Finset.mem_univ,
            true_and] at hj
          exact hx (Fin.le_def.mpr (by simp only [m]; omega))

/-- For a monotone `y`, the sum over any `k`-element set is at least the sum of the first `k`
values. -/
theorem sum_finPrefix_le_sum_of_monotone {n : ℕ} {y : Fin n → ℝ} (hy : Monotone y)
    (s : Finset (Fin n)) : ∑ j ∈ finPrefix n s.card, y j ≤ ∑ j ∈ s, y j := by
  have := sum_le_sum_finPrefix_of_antitone (x := fun j => -y j)
    (fun _ _ h => neg_le_neg (hy h)) s
  simpa only [Finset.sum_neg_distrib, neg_le_neg_iff] using this

/-- A vector all of whose prefix sums vanish is zero. -/
theorem eq_zero_of_finPrefix_sum_eq_zero {n : ℕ} {u : Fin n → ℤ}
    (h : ∀ k ≤ n, ∑ j ∈ finPrefix n k, u j = 0) (j : Fin n) : u j = 0 := by
  have h1 := h ((j : ℕ) + 1) j.isLt
  have h0 := h j j.isLt.le
  rw [finPrefix_succ, Finset.sum_insert (by simp [finPrefix])] at h1
  linarith

end Combinatorics

/-- A complex character datum is determined by its weight and exponent. -/
theorem complexCharacterData_eq_of_weight_exponent {a b : ComplexCharacterData}
    (hw : a.weight = b.weight) (he : a.exponent = b.exponent) : a = b := by
  obtain ⟨χa, wa, ea, ha⟩ := a
  obtain ⟨χb, wb, eb, hb⟩ := b
  simp only at hw he
  subst hw he
  have hχ : χa = χb := ContinuousMonoidHom.ext fun z => Units.ext (by rw [ha z, hb z])
  subst hχ
  rfl

/-- Proof of the reduction. -/
theorem complexStandardOppositeOrderHomReduction :
    ComplexStandardOppositeOrderHomReductionStatement := by
  intro hE hTP n ds cs T hds hcs hord hcord hT hint
  obtain ⟨d, rfl⟩ : ∃ d : Fin n → ComplexCharacterData, List.ofFn d = ds :=
    ⟨fun j => ds.get (Fin.cast hds.symm j), by subst hds; simp⟩
  obtain ⟨c, rfl⟩ : ∃ c : Fin n → ComplexCharacterData, List.ofFn c = cs :=
    ⟨fun j => cs.get (Fin.cast hcs.symm j), by subst hcs; simp⟩
  obtain ⟨σ, u, v, hu, hv, hcd⟩ := hE n d c T hT hint
  obtain ⟨T', hT', hint'⟩ := hTP n d c T hT hint
  obtain ⟨τ, u', v', hu', hv', hdc⟩ := hE n _ _ T' hT' hint'
  set x : Fin n → ℝ := fun j => (d j).exponent.re with hxdef
  set y : Fin n → ℝ := fun j => (c j).exponent.re with hydef
  set w : Fin n → ℝ := fun j => ((u j + v j : ℤ) : ℝ) with hwdef
  set w' : Fin n → ℝ := fun j => ((u' j + v' j : ℤ) : ℝ) with hw'def
  have hx : Antitone x := by
    intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact List.pairwise_ofFn.mp hord h
    · rw [h]
  have hy : Monotone y := by
    intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact List.pairwise_ofFn.mp hcord h
    · rw [h]
  have hyx : ∀ j, y j = x (σ j) + w j / 2 := by
    intro j
    have := congrArg Complex.re (hcd j).1
    simpa [x, y, w] using this
  have hxy : ∀ j, x j = y (τ j) - w' j / 2 := by
    intro j
    have := congrArg Complex.re (hdc j).1
    simp [complexCharacterDataInv, x, y, w'] at this ⊢
    linarith
  have hW : ∀ k, 0 ≤ ∑ j ∈ finPrefix n k, w j := by
    intro k
    have : (0 : ℤ) ≤ ∑ j ∈ finPrefix n k, (u j + v j) := by
      rw [Finset.sum_add_distrib]; exact add_nonneg (hu.1 k) (hv.1 k)
    simp only [w]
    exact_mod_cast this
  have hW' : ∀ k, 0 ≤ ∑ j ∈ finPrefix n k, w' j := by
    intro k
    have : (0 : ℤ) ≤ ∑ j ∈ finPrefix n k, (u' j + v' j) := by
      rw [Finset.sum_add_distrib]; exact add_nonneg (hu'.1 k) (hv'.1 k)
    simp only [w']
    exact_mod_cast this
  have hWtot : ∑ j, w j = 0 := by
    have : ∑ j, (u j + v j) = 0 := by rw [Finset.sum_add_distrib, hu.2, hv.2, add_zero]
    simpa [w] using congrArg (fun z : ℤ => (z : ℝ)) this
  have htot : ∑ j, y j = ∑ j, x j := by
    simp only [hyx, Finset.sum_add_distrib, ← Finset.sum_div, hWtot, zero_div, add_zero]
    exact Equiv.sum_comp σ x
  -- the key inequality: every prefix sum of `w` vanishes
  have key : ∀ k ≤ n, ∑ j ∈ finPrefix n k, w j ≤ 0 := by
    intro k hk
    set s : Finset (Fin n) := (finPrefix n k).map σ.toEmbedding with hs
    set t : Finset (Fin n) := (finPrefix n (n - k)).map τ.toEmbedding with ht
    have hscard : sᶜ.card = n - k := by
      rw [Finset.card_compl, Finset.card_map, card_finPrefix hk, Fintype.card_fin]
    have htcard : tᶜ.card = k := by
      rw [Finset.card_compl, Finset.card_map, card_finPrefix (Nat.sub_le n k),
        Fintype.card_fin]
      omega
    have h1 : ∑ j ∈ finPrefix n k, y j =
        ∑ j ∈ s, x j + (∑ j ∈ finPrefix n k, w j) / 2 := by
      simp only [hyx, Finset.sum_add_distrib, ← Finset.sum_div, s, Finset.sum_map,
        Equiv.coe_toEmbedding]
    have h2 : ∑ j ∈ finPrefix n (n - k), x j =
        ∑ j ∈ t, y j - (∑ j ∈ finPrefix n (n - k), w' j) / 2 := by
      simp only [hxy, Finset.sum_sub_distrib, ← Finset.sum_div, t, Finset.sum_map,
        Equiv.coe_toEmbedding]
    have h3 : ∑ j ∈ sᶜ, x j ≤ ∑ j ∈ finPrefix n (n - k), x j := by
      simpa only [hscard] using sum_le_sum_finPrefix_of_antitone hx sᶜ
    have h4 : ∑ j ∈ finPrefix n k, y j ≤ ∑ j ∈ tᶜ, y j := by
      simpa only [htcard] using sum_finPrefix_le_sum_of_monotone hy tᶜ
    have h5 := Finset.sum_add_sum_compl s x
    have h6 := Finset.sum_add_sum_compl t y
    have h7 := hW' (n - k)
    linarith
  have hUV : ∀ k ≤ n, ∑ j ∈ finPrefix n k, u j = 0 ∧ ∑ j ∈ finPrefix n k, v j = 0 := by
    intro k hk
    have hle : ∑ j ∈ finPrefix n k, (u j + v j) ≤ 0 := by
      have := key k hk
      have hc : ∑ j ∈ finPrefix n k, w j = ((∑ j ∈ finPrefix n k, (u j + v j) : ℤ) : ℝ) := by
        simp [w]
      rw [hc] at this
      exact_mod_cast this
    rw [Finset.sum_add_distrib] at hle
    have h1 : 0 ≤ ∑ j ∈ finPrefix n k, u j := hu.1 k
    have h2 : 0 ≤ ∑ j ∈ finPrefix n k, v j := hv.1 k
    constructor <;> omega
  have hu0 : ∀ j, u j = 0 := eq_zero_of_finPrefix_sum_eq_zero fun k hk => (hUV k hk).1
  have hv0 : ∀ j, v j = 0 := eq_zero_of_finPrefix_sum_eq_zero fun k hk => (hUV k hk).2
  have hc : c = d ∘ σ := by
    funext j
    apply complexCharacterData_eq_of_weight_exponent
    · rw [(hcd j).2, hu0 j, hv0 j]; simp
    · rw [(hcd j).1, hu0 j, hv0 j]; simp
  rw [hc]
  exact (σ.ofFn_comp_perm d).symm

end Langlands.Archimedean
