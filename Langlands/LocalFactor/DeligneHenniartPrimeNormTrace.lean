import Langlands.ClassFieldTheory.Local.PrimeRamifiedTraceIdealsProof
import Langlands.ClassFieldTheory.Local.PrimeNormTraceExpansionProof
import Langlands.ClassFieldTheory.Local.PrimeGradedNormFromArithmeticProof

/-! # First-order norm and trace bounds above a prime ramification break -/

noncomputable section

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

open Langlands.LocalClassField

universe u v

variable {p : ℕ} [Fact p.Prime]
variable (K : PadicField.{u} p) (L : PadicField.{v} p)
variable [Algebra K.Carrier L.Carrier] [IsScalarTower (Padic p) K.Carrier L.Carrier]

/-- The first-order norm and trace ideal bounds for a prime totally ramified
extension above its supplied full single-break pattern. -/
def PrimeNormTraceIdealBoundsStatement
    [FiniteDimensional K.Carrier L.Carrier] [IsGalois K.Carrier L.Carrier] : Prop :=
  ∀ (_hprime : Nat.Prime (Module.finrank K.Carrier L.Carrier))
    (_htot : L.canonicalTopologicalData.ramificationIndex =
      Module.finrank K.Carrier L.Carrier * K.canonicalTopologicalData.ramificationIndex)
    (t : ℕ)
    (_hpat : ∀ i : ℕ,
      Langlands.Ramification.Padic.lowerRamificationGroup
        L.canonicalTopologicalData K.Carrier i = if i ≤ t then ⊤ else ⊥)
    (n : ℕ) (_hnt : t < n)
    (x : L.canonicalTopologicalData.Integers)
    (_hx : x ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^
      (t + Module.finrank K.Carrier L.Carrier * (n - t))),
    (∃ a : K.canonicalTopologicalData.Integers,
      a ∈ IsLocalRing.maximalIdeal K.canonicalTopologicalData.Integers ^ n ∧
      (a : K.Carrier) = Algebra.trace K.Carrier L.Carrier (x : L.Carrier)) ∧
    (∃ r : K.canonicalTopologicalData.Integers,
      r ∈ IsLocalRing.maximalIdeal K.canonicalTopologicalData.Integers ^ (n + 1) ∧
      (r : K.Carrier) = Algebra.norm K.Carrier (1 + (x : L.Carrier)) - 1 -
        Algebra.trace K.Carrier L.Carrier (x : L.Carrier))

variable [FiniteDimensional K.Carrier L.Carrier] [IsGalois K.Carrier L.Carrier]

/-- Above the single break of a prime totally ramified extension, the trace
has depth `n` and the first-order norm remainder has depth `n + 1`.
The input may lie anywhere in the indicated ideal power, including zero. -/
theorem prime_normTrace_ideal_bounds : PrimeNormTraceIdealBoundsStatement K L := by
  intro hprime htot t hpat n hnt x hx
  let ell := Module.finrank K.Carrier L.Carrier
  let m := t + ell * (n - t)
  have hindices := PrimeGradedNorm.trace_indices ell t n hprime.pos hnt.le
  simp only [show ¬ n ≤ t by omega, ↓reduceIte] at hindices
  have hnm : n + 1 ≤ m := by
    have he := hprime.two_le
    have hn : t + (n - t) = n := by omega
    dsimp only [m]
    nlinarith [Nat.mul_le_mul_right (n - t) he]
  have hmpos : 1 ≤ m := by omega
  have hrem : n + 1 ≤ ((t + 1) * (ell - 1) + 2 * m) / ell := by
    apply hindices.2.ge.trans
    exact Nat.div_le_div_right (by dsimp only [m] at *; omega)
  constructor
  · exact PrimeGradedNorm.trace_bound K L htot primeRamifiedTraceIdeals hprime t hpat
      m n hindices.1.ge x hx
  · obtain ⟨z, hz, heq⟩ := primeNormTraceExpansion p K L hprime htot m x hx
    obtain ⟨c, hc, hct⟩ := PrimeGradedNorm.trace_bound K L htot
      primeRamifiedTraceIdeals hprime t hpat (2 * m) (n + 1) hrem z hz
    let b := PrimeGradedNorm.integerNorm K L x
    have hb : b ∈ IsLocalRing.maximalIdeal K.canonicalTopologicalData.Integers ^ (n + 1) :=
      Ideal.pow_le_pow_right hnm (PrimeGradedNorm.integerNorm_mem_pow K L htot m x hx)
    refine ⟨b + c, Ideal.add_mem _ hb hc, ?_⟩
    change Algebra.norm K.Carrier (x : L.Carrier) + (c : K.Carrier) = _
    rw [hct]
    linear_combination -heq

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
