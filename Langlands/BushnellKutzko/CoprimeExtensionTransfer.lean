import Mathlib.GroupTheory.Transfer
import Mathlib.Data.Int.GCD

/-! # Scalar retractions from finite-index transfer -/

noncomputable section

namespace Langlands.BushnellKutzko

universe u v

section Transfer

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]
  {H N : Subgroup G} [H.FiniteIndex] [N.Normal]

/-- Transferring a character trivial on a normal subgroup preserves triviality there. -/
theorem transfer_trivial_on_normal (χ : H →* A) (hχ : N.subgroupOf H ≤ χ.ker)
    {g : G} (hg : g ∈ N) : χ.transfer g = 1 := by
  classical
  let _ := H.fintypeQuotientOfFiniteIndex
  let _ : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) :=
    Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  apply Finset.prod_eq_one
  intro q _
  apply hχ
  change q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out ∈ N
  simpa only [inv_inv] using (inferInstance : N.Normal).conj_mem
    (g ^ Function.minimalPeriod (g • ·) q.out) (pow_mem hg _) q.out.out⁻¹

private theorem transfer_central (χ : H →* A) {g : G} (hg : g ∈ H)
    (hc : ∀ y : G, Commute g y) : χ.transfer g = χ ⟨g, hg⟩ ^ H.index := by
  have h (k : ℕ) (y : G) (_ : y⁻¹ * g ^ k * y ∈ H) : y⁻¹ * g ^ k * y = g ^ k := by
    rw [mul_assoc, ((hc y).pow_left k).eq, inv_mul_cancel_left]
  rw [MonoidHom.transfer_eq_pow χ g h]
  exact map_pow χ ⟨g, hg⟩ H.index

/-- Transfer from a finite-index subgroup and a coprime character power give a retraction
of the central scalars. Both characters may be required to kill a specified normal subgroup. -/
theorem exists_scalar_retraction_of_coprime (z : A →* G) (hz : ∀ a g, Commute (z a) g)
    (hH : ∀ a, z a ∈ H)
    (χ : H →* A) (hχ : ∀ a, χ ⟨z a, hH a⟩ = a) (hχN : N.subgroupOf H ≤ χ.ker)
    (δ : G →* A) (m : ℕ) (hδ : ∀ a, δ (z a) = a ^ m) (hδN : N ≤ δ.ker)
    (hcop : H.index.Coprime m) : ∃ r : G →* A, (∀ a, r (z a) = a) ∧ N ≤ r.ker := by
  let i := Nat.gcdA H.index m
  let j := Nat.gcdB H.index m
  let r : G →* A := χ.transfer ^ i * δ ^ j
  refine ⟨r, fun a => ?_, fun g hg => ?_⟩
  · change (χ.transfer (z a)) ^ i * (δ (z a)) ^ j = a
    rw [transfer_central χ (hH a) (hz a), hχ, hδ, ← zpow_natCast a H.index,
      ← zpow_natCast a m, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have he : (H.index : ℤ) * i + (m : ℤ) * j = 1 := by
      simpa only [i, j, hcop.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab H.index m).symm
    rw [he, zpow_one]
  · change (χ.transfer g) ^ i * (δ g) ^ j = 1
    rw [transfer_trivial_on_normal χ hχN hg, show δ g = 1 from hδN hg,
      one_zpow, one_zpow, one_mul]

end Transfer

section IntertwinedCharacter

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]
  {H : Subgroup G} [H.FiniteIndex]

/-- Transfer on an element of the subgroup evaluates to the index power if the character agrees
on every conjugate pair inside its subgroup. -/
theorem transfer_eq_pow_of_conjugate_agreement (χ : H →* A)
    (hχ : ∀ (y : G) (x : H) (h : y * x.val * y⁻¹ ∈ H), χ ⟨_, h⟩ = χ x)
    (g : H) : χ.transfer g.val = χ g ^ H.index := by
  classical
  let _ := H.fintypeQuotientOfFiniteIndex
  let _ : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g.val) (G ⧸ H))) :=
    Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  trans ∏ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g.val) (G ⧸ H)),
    (χ g) ^ Function.minimalPeriod (g.val • ·) q.out
  · apply Finset.prod_congr rfl
    intro q _
    have he := hχ q.out.out⁻¹ (g ^ Function.minimalPeriod (g.val • ·) q.out)
      (by
        rw [Subgroup.coe_pow, inv_inv]
        exact QuotientGroup.out_conj_pow_minimalPeriod_mem H g.val q.out)
    rw [map_pow] at he
    simpa only [inv_inv, Subgroup.coe_pow] using he
  · rw [Finset.prod_pow_eq_pow_sum, Subgroup.index_eq_sum_minimalPeriod H g.val]

/-- A character with a supplied exponent coprime to the index extends when it agrees on all
ambient conjugate pairs in the subgroup. -/
theorem exists_character_extension_of_coprime_index (χ : H →* A)
    (hχ : ∀ (y : G) (x : H) (h : y * x.val * y⁻¹ ∈ H), χ ⟨_, h⟩ = χ x)
    (m : ℕ) (hm : ∀ x, χ x ^ m = 1) (hcop : H.index.Coprime m) :
    ∃ ψ : G →* A, ψ.comp H.subtype = χ := by
  let i := Nat.gcdA H.index m
  let j := Nat.gcdB H.index m
  refine ⟨χ.transfer ^ i, MonoidHom.ext (fun x => ?_)⟩
  change (χ.transfer x.val) ^ i = χ x
  rw [transfer_eq_pow_of_conjugate_agreement χ hχ x, ← zpow_natCast (χ x) H.index, ← zpow_mul]
  have hzero : (χ x) ^ ((m : ℤ) * j) = 1 := by rw [zpow_mul, zpow_natCast, hm, one_zpow]
  have he : (H.index : ℤ) * i + (m : ℤ) * j = 1 := by
    simpa only [i, j, hcop.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab H.index m).symm
  rw [← mul_one ((χ x) ^ ((H.index : ℤ) * i)), ← hzero, ← zpow_add, he, zpow_one]

end IntertwinedCharacter

end Langlands.BushnellKutzko
