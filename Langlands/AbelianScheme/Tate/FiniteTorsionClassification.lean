import Langlands.AbelianScheme.Tate.FiniteTorsionStructure
import Langlands.AbelianScheme.Tate.FiniteTorsionDecomposition

/-! # Torsion structure from the orders of divisor-torsion subgroups -/

noncomputable section

namespace Langlands.AbelianScheme.Tate

variable (M : Type*) [AddCommGroup M]

/-- Level one is trivial, for every chosen number of coordinates. -/
def piZmodOneTorsionKernelEquiv (r : ℕ) :
    (Fin r → ZMod 1) ≃+ TorsionKernel M 1 where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv x := by
    apply Subtype.ext
    have hx : x.val = 0 := by
      have hx' : (1 : ℕ) • x.val = 0 := x.property
      simpa only [one_smul] using hx'
    exact hx.symm
  map_add' _ _ := by simp

/-- Divisor-torsion orders determine the structure of every positive torsion level. -/
theorem nonempty_pi_zmod_torsionKernel_equiv_of_divisor_card (r : ℕ) :
    ∀ n : ℕ, 0 < n →
      (∀ d : ℕ, d ∣ n → 0 < d → Nat.card (TorsionKernel M d) = d ^ r) →
      Nonempty ((Fin r → ZMod n) ≃+ TorsionKernel M n) := by
  apply Nat.recOnPosPrimePosCoprime
  · intro p e hp he _ hcard
    have hpe : 0 < p ^ e := pow_pos hp.pos e
    have htot : Nat.card (TorsionKernel M (p ^ e)) = (p ^ e) ^ r :=
      hcard _ dvd_rfl hpe
    let : _root_.Finite (TorsionKernel M (p ^ e)) :=
      Nat.finite_of_card_ne_zero (by rw [htot]; exact ne_of_gt (pow_pos hpe r))
    have hpdiv : p ∣ p ^ e := dvd_pow_self p (Nat.ne_of_gt he)
    apply nonempty_pi_zmod_equiv_of_prime_power_card
      (TorsionKernel M (p ^ e)) p e r hp
      (fun x => by apply Subtype.ext; exact x.property) htot
    exact (Nat.card_congr (torsionKernelIteratedEquiv M hpdiv).toEquiv).trans
      (hcard p hpdiv hp.pos)
  · intro h
    exact (Nat.not_lt_zero _ h).elim
  · intro _ _
    exact ⟨piZmodOneTorsionKernelEquiv M r⟩
  · intro a b ha hb hab iha ihb _ hcard
    obtain ⟨ea⟩ := iha (lt_trans Nat.zero_lt_one ha)
      (fun d hd hdpos => hcard d (dvd_trans hd (dvd_mul_right a b)) hdpos)
    obtain ⟨eb⟩ := ihb (lt_trans Nat.zero_lt_one hb)
      (fun d hd hdpos => hcard d (dvd_trans hd (dvd_mul_left b a)) hdpos)
    exact ⟨(piZmodCoprimeEquiv r hab).trans
      ((ea.prodCongr eb).trans (torsionKernelCoprimeEquiv M hab).symm)⟩

/-- Choose the equivalence proved by the divisor-torsion cardinality criterion. -/
def piZmodTorsionKernelEquivOfDivisorCard (n r : ℕ) (hn : 0 < n)
    (hcard : ∀ d : ℕ, d ∣ n → 0 < d → Nat.card (TorsionKernel M d) = d ^ r) :
    (Fin r → ZMod n) ≃+ TorsionKernel M n :=
  Classical.choice (nonempty_pi_zmod_torsionKernel_equiv_of_divisor_card M r n hn hcard)

end Langlands.AbelianScheme.Tate
