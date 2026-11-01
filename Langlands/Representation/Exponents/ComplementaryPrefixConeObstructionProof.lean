import Langlands.Representation.Exponents.ComplementaryPrefixConeObstructionStatement

/-! # The finite-complement contradiction for positive root cones -/

namespace Langlands.Exponents

open scoped BigOperators

/-- Reindex an exact permuted prefix as the sum over its original indices. -/
theorem partialSum_comp_perm_eq_sum {r : ℕ} (x : Fin r → ℝ)
    (S : Finset (Fin r)) (e : Equiv.Perm (Fin r)) (k : ℕ)
    (he : ∀ i : Fin r, (i : ℕ) < k ↔ e i ∈ S) :
    partialSum (x ∘ e) k = ∑ i ∈ S, x i := by
  classical
  unfold partialSum
  refine Finset.sum_bij (fun i _ => e i) ?_ ?_ ?_ ?_
  · intro i hi
    exact (he i).mp (Finset.mem_filter.mp hi).2
  · intro i _ j _ hij
    exact e.injective hij
  · intro j hj
    refine ⟨e.symm j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      e.apply_symm_apply j⟩
    exact (he (e.symm j)).mpr (by simpa using hj)
  · intro i _
    rfl

/-- Strict positivity for both complementary prefixes contradicts total zero. -/
theorem complementaryPrefixConeObstruction :
    ComplementaryPrefixConeObstructionStatement := by
  intro r x S e f hS hC he hf hxe hxf
  have hSpos : 0 < S.card := Finset.card_pos.mpr hS
  have hCpos : 0 < Sᶜ.card := Finset.card_pos.mpr hC
  have hcard : S.card + Sᶜ.card = r := by
    simp
  have hpS := hxe.2 S.card hSpos (by omega)
  have hpC := hxf.2 Sᶜ.card hCpos (by omega)
  rw [partialSum_comp_perm_eq_sum x S e S.card he] at hpS
  rw [partialSum_comp_perm_eq_sum x Sᶜ f Sᶜ.card hf] at hpC
  have hz : ∑ i, x i = 0 := by
    calc
      ∑ i, x i = ∑ i, x (e i) := (Equiv.sum_comp e x).symm
      _ = 0 := hxe.1
  have htot : (∑ i ∈ S, x i) + (∑ i ∈ Sᶜ, x i) = 0 :=
    (Finset.sum_add_sum_compl S x).trans hz
  linarith

end Langlands.Exponents
