/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
public import Mathlib.GroupTheory.Perm.Fin
import WeilConjectures.AlgebraicGeometry.AlternatingCechPartialSortUnique

/-!
# Advancing a partial sorting permutation by an interval cycle

Source: Stacks Project, Tag 01FM, verification of
`cohomology-equation-first-homotopy` (omitted in the source).
(blueprint: lem-pc-alternating-cech-partial-sort-advance)
-/

@[expose] public section
set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

/-- Deleting the tail copy of the junction advances the partially sorted prefix.

Source: Stacks Project, Tag 01FM, equation 20.23.6.1, labelled-deletion verification.
Proof: Write b=tau^{-1}(sigma(a)). Since tau agrees with sigma before a, injectivity
of sigma implies b>=a. Move tau(b) to position a, shifting entries a,...,b-1 right.
This is tau composed with the inverse interval cycle (a ... b). It agrees with
sigma through a. Its remaining tail is the old increasing tail with tau(b) removed,
so remains increasing. Thus it equals rho: both have the same prefix and their
increasing tails enumerate the same complement. In the junction map, positions
0,...,a are sigma(0),...,sigma(a), and later positions are tau(a),...,tau(p+1).
Deleting position b+1 leaves exactly the moved tuple: below a the prefix is unchanged,
at a the entry is tau(b), from a+1 through b it is tau(k-1), and above b it is tau(k).
These are also the four cases of the inverse interval cycle. This proves both
function equality and permutation equality. If b=a the cycle is identity and the
adjacent duplicate is removed. If a=p+1 the advanced tail is empty and rho=sigma.
(blueprint: lem-pc-alternating-cech-partial-sort-advance) -/
theorem cechPartialSort_advance (p : ℕ) (σ τ ρ : Equiv.Perm (Fin (p + 2)))
    (a : Fin (p + 2)) (hτ : cechPartialSort σ τ a)
    (hρ : (∀ k, k.val < a.val + 1 → ρ k = σ k) ∧
      (∀ i j, a.val + 1 ≤ i.val → i < j → ρ i < ρ j)) :
    cechJunction σ τ a ∘ (τ.symm (σ a)).succ.succAbove = ρ ∧
      ρ = τ * (Fin.cycleIcc a (τ.symm (σ a))).symm  := by
  classical
  let b := τ.symm (σ a)
  have hb : a ≤ b := by
    by_contra h
    have he := hτ.1 b (lt_of_not_ge h)
    rw [show τ b = σ a from τ.apply_symm_apply _] at he
    have := σ.injective he
    omega
  let c := Fin.cycleIcc a b
  have hc_lo (k : Fin (p + 2)) (hk : k < a) : c.symm k = k := by
    apply c.injective
    rw [c.apply_symm_apply]
    exact (Fin.cycleIcc_of_lt hk).symm
  have hc_a : c.symm a = b := by
    apply c.injective
    rw [c.apply_symm_apply]
    exact (Fin.cycleIcc_of_last hb).symm
  have hc_hi (k : Fin (p + 2)) (hk : b < k) : c.symm k = k := by
    apply c.injective
    rw [c.apply_symm_apply]
    exact (Fin.cycleIcc_of_gt hk).symm
  have hc_mid (k : Fin (p + 2)) (hka : a < k) (hkb : k ≤ b) :
      c.symm k = ⟨k.val - 1, by omega⟩ := by
    apply c.injective
    rw [c.apply_symm_apply]
    have h1 : a ≤ (⟨k.val - 1, by omega⟩ : Fin (p + 2)) := by
      change a.val ≤ k.val - 1
      omega
    have h2 : (⟨k.val - 1, by omega⟩ : Fin (p + 2)) < b := by
      change k.val - 1 < b.val
      omega
    rw [show c ⟨k.val - 1, by omega⟩ =
      (⟨k.val - 1, by omega⟩ : Fin (p + 2)) + 1 from
      Fin.cycleIcc_of_ge_of_lt h1 h2]
    apply Fin.ext
    rw [Fin.val_add_one_of_lt' (by omega)]
    change k.val = k.val - 1 + 1
    omega
  let π := τ * c.symm
  have hπ : (∀ k : Fin (p + 2), k.val < a.val + 1 → π k = σ k) ∧
      (∀ i j : Fin (p + 2), a.val + 1 ≤ i.val → i < j → π i < π j) := by
    constructor
    · intro k hk
      change τ (c.symm k) = σ k
      by_cases he : k = a
      · subst k
        rw [hc_a]
        exact τ.apply_symm_apply _
      · have hl : k < a := by
          have hn : k.val ≠ a.val := fun h => he (Fin.ext h)
          change k.val < a.val
          omega
        rw [hc_lo k hl]
        exact hτ.1 k hl
    · intro i j hi hij
      change τ (c.symm i) < τ (c.symm j)
      have hj : a < j := by change a.val < j.val; omega
      have hi' : a < i := by change a.val < i.val; omega
      by_cases hib : i ≤ b
      · rw [hc_mid i hi' hib]
        by_cases hjb : j ≤ b
        · rw [hc_mid j hj hjb]
          apply hτ.2
          · change a.val ≤ i.val - 1; omega
          · change i.val - 1 < j.val - 1; omega
        · rw [hc_hi j (lt_of_not_ge hjb)]
          apply hτ.2
          · change a.val ≤ i.val - 1; omega
          · change i.val - 1 < j.val; omega
      · rw [hc_hi i (lt_of_not_ge hib), hc_hi j (by omega)]
        exact hτ.2 i j (by omega) hij
  have he : cechJunction σ τ a ∘ b.succ.succAbove = π := by
    funext k
    change cechJunction σ τ a (b.succ.succAbove k) = τ (c.symm k)
    by_cases hka : k < a
    · rw [hc_lo k hka, Fin.succAbove_of_castSucc_lt _ _ (by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)]
      simp only [cechJunction, Fin.val_castSucc]
      rw [dite_eq_left (by omega)]
      exact (hτ.1 k hka).symm
    · by_cases hke : k = a
      · subst k
        rw [hc_a, Fin.succAbove_of_castSucc_lt _ _ (by
          simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)]
        simp only [cechJunction, Fin.val_castSucc, le_refl, dite_true]
        exact (τ.apply_symm_apply _).symm
      · have hak : a < k := lt_of_le_of_ne (le_of_not_gt hka) (Ne.symm hke)
        by_cases hkb : k ≤ b
        · rw [hc_mid k hak hkb, Fin.succAbove_of_castSucc_lt _ _ (by
            simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega)]
          simp only [cechJunction, Fin.val_castSucc]
          rw [dite_eq_right (by omega)]
        · rw [hc_hi k (lt_of_not_ge hkb), Fin.succAbove_of_le_castSucc _ _ (by
            simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]; omega)]
          simp only [cechJunction, Fin.val_succ]
          rw [dite_eq_right (by omega)]
          congr 1
  obtain ⟨ρ₀, _, hu⟩ := cechPartialSort_existsUnique (p + 2) σ (a.val + 1) (by omega)
  have hπρ : π = ρ := (hu π hπ).trans (hu ρ hρ).symm
  exact ⟨he.trans (congrArg Equiv.toFun hπρ), hπρ.symm⟩

end AlgebraicGeometry.Scheme
