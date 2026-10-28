import Langlands.ClassFieldTheory.Local.PrimeNormTraceExpansionStatement
import Langlands.ClassFieldTheory.Local.PrimeOrbitProductTraceExpansionProof
import Langlands.LocalFactor.Ramification.Galois
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! The prime-degree determinant norm expansion with an actual trace witness. -/

noncomputable section

namespace Langlands.LocalClassField

universe u v

variable {p : ℕ} [Fact p.Prime]
variable (F : PadicField.{u} p) (L : PadicField.{v} p)
variable [Algebra F.Carrier L.Carrier]
variable [IsScalarTower (Padic p) F.Carrier L.Carrier]

private theorem canonical_integerAutomorphism_mem_maximalIdeal_pow
    (n : ℕ) (σ : Gal(L.Carrier/F.Carrier))
    (y : L.canonicalTopologicalData.Integers)
    (hy : y ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ n) :
    Ramification.Padic.integerAutomorphism L.canonicalTopologicalData F.Carrier σ y ∈
      IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ n := by
  have h := Ideal.mem_map_of_mem
    (Ramification.Padic.integerAutomorphism L.canonicalTopologicalData F.Carrier σ) hy
  simpa only [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal] using h

private theorem canonical_integerAction_preserves_maximalIdeal_pow (n : ℕ) :
    letI := Ramification.Padic.integerAction L.canonicalTopologicalData F.Carrier
    ∀ (σ : Gal(L.Carrier/F.Carrier)) (y : L.canonicalTopologicalData.Integers),
      y ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ n →
        σ • y ∈ IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ n := by
  let := Ramification.Padic.integerAction L.canonicalTopologicalData F.Carrier
  exact canonical_integerAutomorphism_mem_maximalIdeal_pow F L n

variable [FiniteDimensional F.Carrier L.Carrier] [IsGalois F.Carrier L.Carrier]

private theorem canonical_integer_equation_to_norm_trace
    (x z : L.canonicalTopologicalData.Integers)
    (h :
      letI := Ramification.Padic.integerAction L.canonicalTopologicalData F.Carrier
      (∏ σ : Gal(L.Carrier/F.Carrier), (1 + σ • x)) - 1 -
          (∑ σ : Gal(L.Carrier/F.Carrier), σ • x) -
          (∏ σ : Gal(L.Carrier/F.Carrier), σ • x) =
        ∑ σ : Gal(L.Carrier/F.Carrier), σ • z) :
    Algebra.norm F.Carrier (1 + (x : L.Carrier)) - 1 -
        Algebra.trace F.Carrier L.Carrier (x : L.Carrier) -
        Algebra.norm F.Carrier (x : L.Carrier) =
      Algebra.trace F.Carrier L.Carrier (z : L.Carrier) := by
  classical
  let := Ramification.Padic.integerAction L.canonicalTopologicalData F.Carrier
  apply (algebraMap F.Carrier L.Carrier).injective
  simp only [map_sub, map_one, Algebra.norm_eq_prod_automorphisms,
    trace_eq_sum_automorphisms, map_add]
  have hc := congrArg
    (fun y : L.canonicalTopologicalData.Integers => (y : L.Carrier)) h
  change
    L.canonicalTopologicalData.Integers.subtype
      ((∏ σ : Gal(L.Carrier/F.Carrier), (1 + σ • x)) - 1 -
          (∑ σ : Gal(L.Carrier/F.Carrier), σ • x) -
          (∏ σ : Gal(L.Carrier/F.Carrier), σ • x)) =
      L.canonicalTopologicalData.Integers.subtype
        (∑ σ : Gal(L.Carrier/F.Carrier), σ • z) at hc
  have hcast (σ : Gal(L.Carrier/F.Carrier))
      (y : L.canonicalTopologicalData.Integers) :
      L.canonicalTopologicalData.Integers.subtype (σ • y) = σ (y : L.Carrier) := rfl
  simpa only [map_sub, map_prod, map_sum, map_one, map_add, hcast] using hc

private theorem canonical_maximalIdeal_pow_square (n : ℕ) :
    (IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ n) ^ 2 =
      IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ (2 * n) := by
  rw [← pow_mul, Nat.mul_comm n 2]

/-- The prime-degree norm expansion modulo traces of the doubled maximal-ideal power. -/
theorem primeNormTraceExpansion : PrimeNormTraceExpansion.{u, v} := by
  intro p _ F L _ _ _ _
  dsimp only
  intro hprime _ n x hx
  classical
  let := Ramification.Padic.integerAction L.canonicalTopologicalData F.Carrier
  have hcard : Nat.Prime (Fintype.card Gal(L.Carrier/F.Carrier)) := by
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
    exact hprime
  obtain ⟨z, hz, heq⟩ := primeOrbitProductTraceExpansion
    Gal(L.Carrier/F.Carrier) L.canonicalTopologicalData.Integers hcard
    (IsLocalRing.maximalIdeal L.canonicalTopologicalData.Integers ^ n)
    (canonical_integerAction_preserves_maximalIdeal_pow F L n) x hx
  refine ⟨z, ?_, canonical_integer_equation_to_norm_trace F L x z heq⟩
  simpa only [canonical_maximalIdeal_pow_square] using hz

end Langlands.LocalClassField
