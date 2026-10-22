import Langlands.Geometry.Analytic.DistinguishedNormalization

/-! # Stability of distinguished series under strictly small perturbations -/

noncomputable section

universe u

namespace Langlands.Analytic.RestrictedSeries

variable {A : Type u} [NormedCommRing A] [IsUltrametricDist A]
  [NormOneClass A] [CompleteSpace A]

omit [CompleteSpace A] in
theorem norm_one_add_of_norm_lt_one (a : A) (ha : ‖a‖ < 1) :
    ‖1 + a‖ = 1 := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by
    rw [norm_one]
    exact ne_of_gt ha), norm_one, max_eq_left ha.le]

/-- The inverse of the perturbed leading coefficient is furnished by an
actual convergent geometric series in the complete coefficient ring. -/
theorem isDistinguished_add_of_normalized
    (f : Algebra A) (d : ℕ) (hf : IsNormalizedDistinguished f d)
    (h : Algebra A) (hh : ‖h‖ < 1) :
    IsDistinguished (f + h) d := by
  have hcoeff (n : ℕ) : ‖coeff A n h‖ < 1 :=
    ((norm_le_iff A h (norm_nonneg h)).mp le_rfl n).trans_lt hh
  have hlead : coeff A d (f + h) = 1 + coeff A d h := by
    rw [map_add, hf.1]
  have hnorm : ‖coeff A d (f + h)‖ = 1 := by
    rw [hlead]
    exact norm_one_add_of_norm_lt_one _ (hcoeff d)
  refine ⟨?_, ?_, ?_⟩
  · rw [hlead]
    refine ⟨Units.oneSub (-(coeff A d h)) (by simpa only [norm_neg] using hcoeff d), ?_⟩
    simp
  · intro n
    rw [hnorm, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hf.2.1 n) (hcoeff n).le)
  · intro n hn
    rw [hnorm, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt (hf.2.2 n hn) (hcoeff n))

omit [NormOneClass A] [CompleteSpace A] in
/-- A monic polynomial with unit-ball coefficients is normalized
distinguished at its actual degree, including degree zero. -/
theorem ofPolynomial_isNormalizedDistinguished (p : Polynomial A)
    (hp : p.Monic) (hcoeff : ∀ n, ‖p.coeff n‖ ≤ 1) :
    IsNormalizedDistinguished (ofPolynomial A p) p.natDegree := by
  refine ⟨?_, ?_, ?_⟩
  · rw [coeff_ofPolynomial]
    exact hp.coeff_natDegree
  · intro n
    rw [coeff_ofPolynomial]
    exact hcoeff n
  · intro n hn
    rw [coeff_ofPolynomial, Polynomial.coeff_eq_zero_of_natDegree_lt hn, norm_zero]
    exact zero_lt_one

/-- The polynomial dominant part plus its actual strictly small analytic
remainder is distinguished, with no inverse supplied as a hypothesis. -/
theorem isDistinguished_polynomial_add (p : Polynomial A)
    (hp : p.Monic) (hcoeff : ∀ n, ‖p.coeff n‖ ≤ 1)
    (h : Algebra A) (hh : ‖h‖ < 1) :
    IsDistinguished (ofPolynomial A p + h) p.natDegree :=
  isDistinguished_add_of_normalized _ _ (ofPolynomial_isNormalizedDistinguished p hp hcoeff)
    h hh

variable [NormMulClass A]

/-- A distinguished series remains distinguished when perturbed by less
than the norm of its distinguished coefficient. The perturbed coefficient
unit is constructed, not assumed. -/
theorem IsDistinguished.add_of_norm_lt {f : Algebra A} {d : ℕ}
    (hf : IsDistinguished f d) (h : Algebra A)
    (hh : ‖h‖ < ‖coeff A d f‖) : IsDistinguished (f + h) d := by
  have : Nontrivial A := ⟨⟨0, 1, fun heq => (zero_ne_one : (0 : ℝ) ≠ 1)
    (by simpa only [norm_zero, norm_one] using congrArg norm heq)⟩⟩
  obtain ⟨a, ha⟩ := hf.1
  have hcoeff (n : ℕ) : ‖coeff A n h‖ < ‖coeff A d f‖ :=
    ((norm_le_iff A h (norm_nonneg h)).mp le_rfl n).trans_lt hh
  have hnorm : ‖coeff A d (f + h)‖ = ‖coeff A d f‖ := by
    rw [map_add, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (ne_of_gt (hcoeff d)), max_eq_left (hcoeff d).le]
  have hmul : ‖((a⁻¹ : Aˣ) : A)‖ * ‖(a : A)‖ = 1 := by
    rw [← norm_mul]
    simp
  have hinv : ‖((a⁻¹ : Aˣ) : A)‖⁻¹ = ‖(a : A)‖ := by
    calc
      ‖((a⁻¹ : Aˣ) : A)‖⁻¹ =
          ‖((a⁻¹ : Aˣ) : A)‖⁻¹ * (‖((a⁻¹ : Aˣ) : A)‖ * ‖(a : A)‖) := by
        rw [hmul, mul_one]
      _ = ‖(a : A)‖ := by
        rw [← mul_assoc, inv_mul_cancel₀ (Units.norm_pos a⁻¹).ne', one_mul]
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨a.add (coeff A d h) (by rw [hinv, ha]; exact hcoeff d), ?_⟩
    change (a : A) + coeff A d h = coeff A d (f + h)
    rw [ha, map_add]
  · intro n
    rw [hnorm, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (hf.2.1 n) (hcoeff n).le)
  · intro n hn
    rw [hnorm, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt (hf.2.2 n hn) (hcoeff n))

end Langlands.Analytic.RestrictedSeries
