import Langlands.Representation.Plancherel.LaurentBlockInvariants
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Prime divisors shared by all scalings of a Laurent block -/

noncomputable section

open AddMonoidAlgebra

namespace Langlands.Plancherel.LaurentBlockInvariants

variable {r n : ℕ}

set_option hygiene false in
local notation "First" => AddMonoidAlgebra ℂ (Fin r → ℤ)
set_option hygiene false in
local notation "Product" => AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin n → ℤ))
set_option hygiene false in
local notation "Blocks" => AddMonoidAlgebra First (Fin n → ℤ)

/-- Group the coefficients by their second block exponent. -/
def splitBlocks : Product ≃+* Blocks :=
  (AddMonoidAlgebra.mapDomainRingEquiv ℂ (AddEquiv.prodComm :
    ((Fin r → ℤ) × (Fin n → ℤ)) ≃+ ((Fin n → ℤ) × (Fin r → ℤ)))).trans
    AddMonoidAlgebra.curryRingEquiv

private theorem splitBlocks_single (a : Fin r → ℤ) (b : Fin n → ℤ) (c : ℂ) :
    splitBlocks (single (a, b) c) = single b (single a c) := by
  simp [splitBlocks, AddMonoidAlgebra.mapDomainRingEquiv_single]

private theorem splitBlocks_monomial_mul_firstBlock (b : Fin n → ℤ) (x : First) :
    splitBlocks (single (0, b) 1 * firstBlock x) = single b x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [mul_add, hx, hy, single_add]
  | single a c => simp [splitBlocks_single]

private def blockCharacter (Q : Type*) [CommRing Q] [Algebra ℂ Q]
    (b : Fin n → ℤ) : (Fin n → ℂˣ) →* Q where
  toFun t := algebraMap ℂ Q (↑(∏ i, t i ^ b i : ℂˣ) : ℂ)
  map_one' := by simp
  map_mul' t s := by simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, map_mul]

private theorem blockCharacter_injective (Q : Type*) [CommRing Q] [Nontrivial Q] [Algebra ℂ Q] :
    Function.Injective (blockCharacter (n := n) Q) := by
  intro b d hd
  apply single_left_injective (one_ne_zero : (1 : ℂ) ≠ 0)
  apply sub_eq_zero.mp
  apply finiteLaurent_eq_zero_of_eval_on_open _ isOpen_univ Set.univ_nonempty
  intro t _
  have he := (algebraMap ℂ Q).injective (DFunLike.congr_fun hd t)
  have he' : (∏ i, ((t i ^ b i : ℂˣ) : ℂ)) = ∏ i, ((t i ^ d i : ℂˣ) : ℂ) := by
    change Units.coeHom ℂ (∏ i, t i ^ b i) = Units.coeHom ℂ (∏ i, t i ^ d i) at he
    simpa only [map_prod, Units.coeHom_apply] using he
  simp only [map_sub, finiteLaurentEvaluation_single, one_mul, he', sub_self]

variable (s : (Fin n → ℂˣ) → Product ≃ₐ[ℂ] Product)
  (hs : ∀ t (m : (Fin r → ℤ) × (Fin n → ℤ)) (c : ℂ),
    s t (single m c) = single m (c * ((∏ i, t i ^ m.2 i : ℂˣ) : ℂ)))

include hs in
private theorem scaling_monomial_mul_firstBlock (t : Fin n → ℂˣ) (b : Fin n → ℤ) (x : First) :
    s t (single (0, b) 1 * firstBlock x) =
      (↑(∏ i, t i ^ b i : ℂˣ) : ℂ) • (single (0, b) 1 * firstBlock x) := by
  have hfixed : s t (firstBlock x) = firstBlock (n := n) x := by
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | single a c => simp [hs]
  rw [map_mul, hfixed, hs, one_mul, ← smul_mul_assoc, smul_single', mul_one]

include hs in
/-- If a prime divides every scaling of a nonzero Laurent polynomial,
it divides the first-block inclusion of a nonzero Laurent polynomial. -/
theorem exists_prime_dvd_firstBlock_of_dvd_all_scalings
    (p c : Product) (hp : Prime p) (hc : c ≠ 0) (hdiv : ∀ t, p ∣ s t c) :
    ∃ d : First, d ≠ 0 ∧ p ∣ firstBlock d := by
  classical
  let I : Ideal Product := Ideal.span {p}
  let : I.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  let Q := Product ⧸ I
  let : IsDomain Q := (Ideal.Quotient.isDomain_iff_prime I).mpr inferInstance
  let q : Product →ₐ[ℂ] Q := Ideal.Quotient.mkₐ ℂ I
  have hq (x : Product) : q x = 0 ↔ p ∣ x := by
    change Ideal.Quotient.mk I x = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  let f := splitBlocks c
  have hdec : c = ∑ b ∈ f.coeff.support, single (0, b) 1 * firstBlock (f.coeff b) := by
    apply splitBlocks.injective
    rw [map_sum]
    simp_rw [splitBlocks_monomial_mul_firstBlock]
    exact f.sum_coeff_single.symm
  have hcomb : ∑ b ∈ f.coeff.support, q (single (0, b) 1 * firstBlock (f.coeff b)) •
      (blockCharacter Q b : (Fin n → ℂˣ) → Q) = 0 := by
    funext t
    have ht := (hq _).mpr (hdiv t)
    have he : q (s t c) = q (s t (∑ b ∈ f.coeff.support, single (0, b) 1 * firstBlock (f.coeff b))) :=
      congrArg (fun x => q (s t x)) hdec
    have hz := he.symm.trans ht
    simp only [map_sum, scaling_monomial_mul_firstBlock s hs, map_smul] at hz
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    calc
      _ = ∑ b ∈ f.coeff.support, (↑(∏ i, t i ^ b i : ℂˣ) : ℂ) •
          q (single (0, b) 1 * firstBlock (f.coeff b)) := by
        apply Finset.sum_congr rfl
        intro b _
        change q (single (0, b) 1 * firstBlock (f.coeff b)) *
          algebraMap ℂ Q (↑(∏ i, t i ^ b i : ℂˣ) : ℂ) = _
        let weight : ℂ := ↑(∏ i, t i ^ b i : ℂˣ)
        let term : Product := single (0, b) 1 * firstBlock (f.coeff b)
        exact (mul_comm (q term) (algebraMap ℂ Q weight)).trans
          (Algebra.smul_def (R := ℂ) (A := Q) weight (q term)).symm
      _ = 0 := hz
  have hind := (linearIndependent_monoidHom (Fin n → ℂˣ) Q).comp (blockCharacter Q)
    (blockCharacter_injective Q)
  have hz := (linearIndependent_iff'.mp hind) f.coeff.support _ hcomb
  have hfnz : f.coeff ≠ 0 := fun hzero => hc ((map_eq_zero_iff _ splitBlocks.injective).mp
    (AddMonoidAlgebra.coeff_injective (hzero.trans AddMonoidAlgebra.coeff_zero.symm)))
  obtain ⟨b, hb⟩ := Finsupp.support_nonempty_iff.mpr hfnz
  have hunit : IsUnit (single (0, b) 1 : Product) := by
    refine isUnit_iff_exists_inv.mpr ⟨single (0, -b) 1, ?_⟩
    simp [AddMonoidAlgebra.one_def]
    rfl
  have hnot : ¬ p ∣ (single (0, b) 1 : Product) :=
    fun hd => hp.not_isUnit (isUnit_of_dvd_unit hd hunit)
  refine ⟨f.coeff b, Finsupp.mem_support_iff.mp hb, ?_⟩
  exact (hp.dvd_mul.mp ((hq _).mp (hz b hb))).resolve_left hnot

end Langlands.Plancherel.LaurentBlockInvariants
