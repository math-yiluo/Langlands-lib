import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.NumberTheory.Padics.PadicNumbers

/-! # Cardinalities of kernels in finite groups

* `card_ker_eq_card_quotient_range`: an endomorphism of a finite additive group has kernel
  and cokernel of the same cardinality.
* `norm_card_eq_norm_card_ker_pow`: the `p`-adic norm of the order of a finite commutative
  group equals that of its subgroup of elements killed by `p ^ N`, once `N` is at least the
  order.
-/

noncomputable section

namespace Langlands.Algebra.PadicLattice

/-- Kernel and cokernel of an endomorphism of a finite additive group have the same
cardinality. -/
theorem card_ker_eq_card_quotient_range {L : Type*} [AddCommGroup L] [Finite L]
    (f : L →+ L) : Nat.card f.ker = Nat.card (L ⧸ f.range) := by
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  have h2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.range
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv] at h1
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  rw [h1, mul_comm] at h2
  exact Nat.eq_of_mul_eq_mul_right hpos h2

variable {p : ℕ} [Fact p.Prime]

/-- In a finite commutative group of order at most `N`, the `p`-adic norm of the order is the
`p`-adic norm of the order of the subgroup killed by `p ^ N`. -/
theorem norm_card_eq_norm_card_ker_pow {K : Type*} [CommGroup K] [Finite K] (N : ℕ)
    (hN : Nat.card K ≤ N) :
    ‖((Nat.card K : ℕ) : ℚ_[p])‖ =
      ‖((Nat.card (powMonoidHom (p ^ N) : K →* K).ker : ℕ) : ℚ_[p])‖ := by
  let φ : K →* K := powMonoidHom (p ^ N)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  have hcop : p.Coprime (Nat.card φ.range) := by
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    intro hdvd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := φ.range) p hdvd
    obtain ⟨x, hx⟩ := y.property
    have ho : orderOf x ≠ 0 := (orderOf_pos x).ne'
    obtain ⟨a, c, hpc, hac⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho p
      (Nat.Prime.ne_one Fact.out)
    have hle : orderOf x ≤ N := orderOf_le_card.trans hN
    · have ha : a ≤ N := by
        have h3 : p ^ a ≤ orderOf x := Nat.le_of_dvd (orderOf_pos x) ⟨c, hac⟩
        have h4 : a < p ^ a := Nat.lt_pow_self (Nat.Prime.one_lt Fact.out)
        omega
      have hyc : y ^ c = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hx]
        change (x ^ (p ^ N)) ^ c = 1
        rw [← pow_mul]
        apply orderOf_dvd_iff_pow_eq_one.mp
        rw [hac]
        exact Nat.mul_dvd_mul (pow_dvd_pow p ha) dvd_rfl
      have := orderOf_dvd_of_pow_eq_one hyc
      rw [hy] at this
      exact hpc this
  have hnorm : ‖((Nat.card φ.range : ℕ) : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr hcop
  rw [h1, Nat.cast_mul, norm_mul, hnorm, one_mul]

end Langlands.Algebra.PadicLattice
