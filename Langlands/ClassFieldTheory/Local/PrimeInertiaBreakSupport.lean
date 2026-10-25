import Langlands.LocalFactor.Ramification.Herbrand.Finite
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! Prime-order lower filtrations and the constructed inverse Herbrand function. -/

noncomputable section

namespace Langlands.LocalClassField

open Langlands.Ramification

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (L : PadicField.{v} p)
  [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
  [FiniteDimensional F.Carrier L.Carrier] [IsGalois F.Carrier L.Carrier]
  (T : L.TopologicalData)

/-- A prime-order actual lower filtration with total inertia has one break. -/
theorem exists_prime_lowerRamificationGroup_pattern
    (hell : Nat.Prime (Module.finrank F.Carrier L.Carrier))
    (hinertia : Padic.inertia T F.Carrier = ⊤) :
    ∃ t : ℕ,
      (∀ i : ℕ, Padic.lowerRamificationGroup T F.Carrier i =
        if i ≤ t then ⊤ else ⊥) ∧
      (0 < t ↔ Padic.lowerRamificationGroup T F.Carrier 1 = ⊤) := by
  classical
  have hcard := IsGalois.card_aut_eq_finrank F.Carrier L.Carrier
  have : Fact (Nat.card Gal(L.Carrier/F.Carrier)).Prime := ⟨by rwa [hcard]⟩
  have : Nontrivial Gal(L.Carrier/F.Carrier) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; exact hell.one_lt)
  have hb : ∃ b : ℕ, Padic.lowerRamificationGroup T F.Carrier b = ⊥ := by
    obtain ⟨b, hb⟩ := Padic.exists_lowerRamificationGroup_eq_bot T F.Carrier
    exact ⟨b, hb b le_rfl⟩
  have hzero : Padic.lowerRamificationGroup T F.Carrier 0 = ⊤ := by
    rw [Padic.lowerRamificationGroup_zero, hinertia]
  have hbpos : 0 < Nat.find hb := by
    by_contra h
    have hfind : Nat.find hb = 0 := by omega
    have h := Nat.find_spec hb
    rw [hfind, hzero] at h
    exact top_ne_bot h
  let t := Nat.find hb - 1
  have hpat : ∀ i : ℕ, Padic.lowerRamificationGroup T F.Carrier i =
      if i ≤ t then ⊤ else ⊥ := by
    intro i
    by_cases hi : i ≤ t
    · rw [ite_eq_left hi]
      apply (Padic.lowerRamificationGroup T F.Carrier i).eq_bot_or_eq_top_of_prime_card.resolve_left
      exact Nat.find_min hb (by dsimp [t] at hi; omega)
    · rw [ite_eq_right hi]
      apply le_bot_iff.mp
      rw [← Nat.find_spec hb]
      exact Padic.lowerRamificationGroup_antitone T F.Carrier (by dsimp [t] at hi; omega)
  refine ⟨t, hpat, ?_⟩
  rw [hpat 1]
  by_cases ht : 0 < t
  · simp [show 1 ≤ t by omega, ht]
  · simp [show ¬ 1 ≤ t by omega, ht, bot_ne_top]

/-- The inverse Herbrand function at natural inputs for an actual single-break
filtration of prime degree. -/
theorem herbrandPsi_nat_of_prime_pattern
    (hell : Nat.Prime (Module.finrank F.Carrier L.Carrier)) (t : ℕ)
    (hpat : ∀ i : ℕ, Padic.lowerRamificationGroup T F.Carrier i =
      if i ≤ t then ⊤ else ⊥) (n : ℕ) :
    Padic.herbrandPsi T F.Carrier (n : ℝ) =
      ((if n ≤ t then n else t + Module.finrank F.Carrier L.Carrier * (n - t) : ℕ) : ℝ) := by
  have hcard := IsGalois.card_aut_eq_finrank F.Carrier L.Carrier
  have hord : ∀ i : ℕ, Padic.lowerGroupOrder T F.Carrier i =
      if i ≤ t then Module.finrank F.Carrier L.Carrier else 1 := by
    intro i
    unfold Padic.lowerGroupOrder
    rw [hpat i]
    have hcard' : Fintype.card Gal(L.Carrier/F.Carrier) =
        Module.finrank F.Carrier L.Carrier := by simpa only [Nat.card_eq_fintype_card] using hcard
    split <;> simp [hcard']
  have hsum_le (m : ℕ) (hm : m ≤ t) :
      (∑ i ∈ Finset.range m, (Padic.lowerGroupOrder T F.Carrier (i + 1) : ℝ)) =
        (m : ℝ) * Module.finrank F.Carrier L.Carrier := by
    calc
      _ = ∑ _i ∈ Finset.range m, (Module.finrank F.Carrier L.Carrier : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hord, ite_eq_left (by have := Finset.mem_range.mp hi; omega)]
      _ = _ := by simp [nsmul_eq_mul]
  have hsum_add (m : ℕ) :
      (∑ i ∈ Finset.range (t + m), (Padic.lowerGroupOrder T F.Carrier (i + 1) : ℝ)) =
        (t : ℝ) * Module.finrank F.Carrier L.Carrier + m := by
    rw [Finset.sum_range_add, hsum_le t le_rfl]
    congr 1
    calc
      _ = ∑ _i ∈ Finset.range m, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hord, ite_eq_right (by omega)]
        norm_num
      _ = _ := by simp
  have hphi (m : ℕ) : Padic.herbrandPhi T F.Carrier (m : ℝ) =
      (∑ i ∈ Finset.range m, (Padic.lowerGroupOrder T F.Carrier (i + 1) : ℝ)) /
        Module.finrank F.Carrier L.Carrier := by
    rw [Padic.herbrandPhi_floor T F.Carrier (Nat.cast_nonneg m)]
    simp only [Nat.floor_natCast, sub_self, zero_mul, add_zero, hord 0, Nat.zero_le, ite_true]
  have hell0 : (Module.finrank F.Carrier L.Carrier : ℝ) ≠ 0 := by
    exact_mod_cast hell.ne_zero
  by_cases hn : n ≤ t
  · rw [ite_eq_left hn]
    have h : Padic.herbrandPhi T F.Carrier (n : ℝ) = n := by
      rw [hphi, hsum_le n hn]
      exact mul_div_cancel_right₀ _ hell0
    exact (congrArg (Padic.herbrandPsi T F.Carrier) h).symm.trans
      (Padic.herbrandPsi_herbrandPhi T F.Carrier _)
  · rw [ite_eq_right hn]
    have h : Padic.herbrandPhi T F.Carrier
        ((t + Module.finrank F.Carrier L.Carrier * (n - t) : ℕ) : ℝ) = n := by
      rw [hphi, hsum_add]
      push_cast
      rw [Nat.cast_sub (by omega : t ≤ n)]
      field_simp
      ring
    exact (congrArg (Padic.herbrandPsi T F.Carrier) h).symm.trans
      (Padic.herbrandPsi_herbrandPhi T F.Carrier _)

end Langlands.LocalClassField
