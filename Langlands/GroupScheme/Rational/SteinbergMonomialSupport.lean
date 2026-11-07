import Langlands.GroupScheme.Rational.SteinbergCoefficientTrace

/-! # Actual monomial coefficients and dominant support of Steinberg traces -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators Matrix

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {r : ℕ}
    (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (s : p.SimpleReflectionRepresentatives)
    {n : Type} [Fintype n] [DecidableEq n] (ρ : MatrixRepresentation G n)

/-- The monomial exponent of a bounded tuple of actual root-coefficient degrees. -/
def steinbergCoefficientExponent (m : steinbergCoefficientDegrees e x ρ) : Fin r →₀ ℕ :=
  Finsupp.indicator Finset.univ (fun j _ => (m j : ℕ))

@[simp] theorem steinbergCoefficientExponent_apply
    (m : steinbergCoefficientDegrees e x ρ) (j : Fin r) :
    steinbergCoefficientExponent e x ρ m j = (m j : ℕ) :=
  Finsupp.indicator_of_mem (Finset.mem_univ j) _

/-- Distinct bounded degree tuples give distinct monomial exponents. -/
theorem steinbergCoefficientExponent_injective :
    Function.Injective (steinbergCoefficientExponent e x ρ) := by
  intro m m' h
  funext j
  apply Fin.ext
  simpa only [steinbergCoefficientExponent_apply] using
    congrArg (fun d : Fin r →₀ ℕ => d j) h

/-- The actual trace coefficient at a bounded degree tuple is exactly the
trace of its ordered coefficient matrix. -/
theorem steinbergRestriction_trace_coeff_at_exponent
    (m : steinbergCoefficientDegrees e x ρ) :
    (steinbergRestriction e x s ρ.traceClassFunction).coeff
        (steinbergCoefficientExponent e x ρ m) =
      Matrix.trace (steinbergCoefficientMatrix x s ρ e (fun j => m j)) := by
  classical
  have hc (m' : steinbergCoefficientDegrees e x ρ) :
      (∏ j, (MvPolynomial.X j : MvPolynomial (Fin r) k) ^ (m' j : ℕ)).coeff
          (steinbergCoefficientExponent e x ρ m) = if m = m' then 1 else 0 := by
    rw [MvPolynomial.coeff_prod_X_pow]
    change (if steinbergCoefficientExponent e x ρ m =
      steinbergCoefficientExponent e x ρ m' then 1 else 0) = _
    simp only [(steinbergCoefficientExponent_injective e x ρ).eq_iff]
  rw [steinbergRestriction_trace_eq_sum_coefficients, MvPolynomial.coeff_sum]
  simp_rw [mul_comm _ (MvPolynomial.C _), MvPolynomial.coeff_C_mul, hc]
  simp

/-- Every nonzero monomial coefficient in the actual restricted trace comes
from an occurring dominant weight with precisely those simple-coroot degrees. -/
theorem exists_dominant_weight_of_steinbergRestriction_trace_coeff_ne_zero
    (d : Fin r →₀ ℕ)
    (hcoeff : (steinbergRestriction e x s ρ.traceClassFunction).coeff d ≠ 0) :
    ∃ lam : characterLattice p.torus,
      p.representationWeightSpace ρ lam ≠ ⊥ ∧ p.IsDominantWeight lam ∧
        ∀ j, (d j : ℤ) = p.rootDatum.toLinearMap lam (p.rootDatum.coroot (e j)) := by
  classical
  by_contra h
  apply hcoeff
  rw [steinbergRestriction_trace_eq_sum_coefficients, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro m hm
  rw [mul_comm _ (MvPolynomial.C _), MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_prod_X_pow]
  change Matrix.trace (steinbergCoefficientMatrix x s ρ e (fun j => m j)) *
    (if d = steinbergCoefficientExponent e x ρ m then 1 else 0) = 0
  split_ifs with hdm
  · rw [mul_one]
    apply steinbergCoefficientMatrix_trace_eq_zero_of_no_weight e x s ρ
    intro lam hmem hpair
    apply h
    refine ⟨lam, hmem,
      isDominantWeight_of_coefficientWeightPath_closed e _ lam
        ((coefficientWeightPath_closed_iff e _ lam).mpr hpair), ?_⟩
    intro j
    rw [hdm, steinbergCoefficientExponent_apply]
    exact hpair j
  · exact mul_zero _

end Langlands.GroupScheme.SplitPinning
