import Mathlib.Analysis.Polynomial.Norm
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Normed.Group.Ultra

/-! # Contractive polynomial division for the Gauss norm -/

noncomputable section

universe u

namespace Langlands.Analytic

open Polynomial

variable {A : Type u} [NormedCommRing A] [IsUltrametricDist A]

omit [IsUltrametricDist A] in
/-- A coefficient bound is exactly a bound on the polynomial Gauss norm. -/
theorem polynomial_supNorm_le_iff (p : Polynomial A) (C : ℝ) :
    p.supNorm ≤ C ↔ ∀ i, ‖p.coeff i‖ ≤ C := by
  constructor
  · intro h i
    exact (p.le_supNorm i).trans h
  · intro h
    obtain ⟨i, hi⟩ := p.exists_eq_supNorm
    rw [hi]
    exact h i

/-- The actual long-division recursion preserves every nonnegative coefficient
bound when the divisor is monic and its coefficients lie in the norm unit ball. -/
private theorem divModByMonicAux_coeff_bound
    (q : Polynomial A) (hq : q.Monic) (hunit : ∀ i, ‖q.coeff i‖ ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ p : Polynomial A, (∀ i, ‖p.coeff i‖ ≤ C) →
      (∀ i, ‖(p.divModByMonicAux hq).1.coeff i‖ ≤ C) ∧
      (∀ i, ‖(p.divModByMonicAux hq).2.coeff i‖ ≤ C)
  | p, hp => by
    classical
    rw [Polynomial.divModByMonicAux]
    split_ifs with h
    · let z := Polynomial.C p.leadingCoeff * X ^ (p.natDegree - q.natDegree)
      have hz : ∀ i, ‖z.coeff i‖ ≤ C := by
        intro i
        simp only [z, coeff_C_mul, coeff_X_pow]
        split_ifs
        · simpa using hp p.natDegree
        · simpa using hC
      have hr : ∀ i, ‖(p - q * z).coeff i‖ ≤ C := by
        intro i
        rw [coeff_sub]
        apply (show ‖p.coeff i - (q * z).coeff i‖ ≤
            max ‖p.coeff i‖ ‖(q * z).coeff i‖ from by
          simpa only [sub_eq_add_neg, norm_neg] using
            IsUltrametricDist.norm_add_le_max (p.coeff i) (-(q * z).coeff i)).trans
        apply max_le (hp i)
        rw [show q * z = (q * Polynomial.C p.leadingCoeff) *
          X ^ (p.natDegree - q.natDegree) by simp [z, mul_assoc]]
        rw [coeff_mul_X_pow']
        split_ifs
        · rw [coeff_mul_C]
          exact (norm_mul_le _ _).trans
            ((mul_le_mul_of_nonneg_right (hunit _) (norm_nonneg _)).trans
              (by simpa using hp p.natDegree))
        · simpa using hC
      have hrec := divModByMonicAux_coeff_bound q hq hunit C hC (p - q * z) hr
      refine ⟨fun i => ?_, hrec.2⟩
      change ‖(z + (Polynomial.divModByMonicAux (p - q * z) hq).1).coeff i‖ ≤ C
      rw [coeff_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz i) (hrec.1 i))
    · exact ⟨fun i => by simpa using hC, hp⟩
  termination_by p => p
  decreasing_by exact Polynomial.div_wf_lemma h hq

/-- Both long-division outputs have Gauss norm at most that of the input. -/
theorem polynomial_division_supNorm_le (p q : Polynomial A) (hq : q.Monic)
    (hunit : ∀ i, ‖q.coeff i‖ ≤ 1) :
    (p /ₘ q).supNorm ≤ p.supNorm ∧ (p %ₘ q).supNorm ≤ p.supNorm := by
  obtain ⟨hdiv, hmod⟩ :=
    divModByMonicAux_coeff_bound q hq hunit p.supNorm p.supNorm_nonneg
      p p.le_supNorm
  constructor
  · apply (polynomial_supNorm_le_iff _ _).mpr
    simpa only [Polynomial.divByMonic, dite_eq_left hq] using hdiv
  · apply (polynomial_supNorm_le_iff _ _).mpr
    simpa only [Polynomial.modByMonic, dite_eq_left hq] using hmod

/-- Polynomial division by a unit-ball monic polynomial has unique quotient
and remainder, and each output satisfies the sharp unit-radius bound. -/
theorem existsUnique_polynomial_division [Nontrivial A]
    (p q : Polynomial A) (hq : q.Monic) (hunit : ∀ i, ‖q.coeff i‖ ≤ 1) :
    ∃! qr : Polynomial A × Polynomial A,
      p = q * qr.1 + qr.2 ∧ qr.2.degree < q.degree ∧
      qr.1.supNorm ≤ p.supNorm ∧ qr.2.supNorm ≤ p.supNorm := by
  refine ⟨(p /ₘ q, p %ₘ q), ?_, ?_⟩
  · exact ⟨by simpa [add_comm] using (modByMonic_add_div p q).symm,
      degree_modByMonic_lt p hq, polynomial_division_supNorm_le p q hq hunit⟩
  · intro qr hqr
    obtain ⟨hdiv, hmod⟩ := div_modByMonic_unique qr.1 qr.2 hq
      ⟨by simpa [add_comm] using hqr.1.symm, hqr.2.1⟩
    exact Prod.ext hdiv.symm hmod.symm

end Langlands.Analytic
