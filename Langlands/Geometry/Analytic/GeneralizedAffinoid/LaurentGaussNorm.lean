import Langlands.Geometry.Analytic.GeneralizedAffinoid.LaurentGaussField
import Langlands.Geometry.Analytic.Spectrum.Definitions
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Polynomial.GaussNorm

/-! # The multiplicative Gauss norm at every positive Laurent radius -/

noncomputable section

universe u

namespace Langlands.Analytic

namespace GaussLaurent

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {t : ℝ} [Fact (0 < t)]

/-- Include an ordinary polynomial among Laurent polynomials. -/
def polynomialInclusion : Polynomial K →+* GaussLaurent K t := Polynomial.toLaurent

omit [IsUltrametricDist K] [Fact (0 < t)] in
@[simp] theorem coeff_polynomialInclusion_nat (p : Polynomial K) (n : ℕ) :
    coeff (polynomialInclusion (t := t) p) (n : ℤ) = p.coeff n := by
  change Finsupp.mapDomain (fun n : ℕ => (n : ℤ)) p.toFinsupp.coeff (n : ℤ) = _
  rw [Finsupp.mapDomain_apply_of_injective Nat.cast_injective]
  rfl

omit [IsUltrametricDist K] [Fact (0 < t)] in
@[simp] theorem coeff_polynomialInclusion_neg (p : Polynomial K) {n : ℤ} (hn : n < 0) :
    coeff (polynomialInclusion (t := t) p) n = 0 := by
  change Finsupp.mapDomain (fun n : ℕ => (n : ℤ)) p.toFinsupp.coeff n = _
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨m, rfl⟩
  change (m : ℤ) < 0 at hn
  exact (not_lt_of_ge (Int.natCast_nonneg m)) hn

/-- The existing Laurent norm restricts to Mathlib's polynomial Gauss norm. -/
theorem norm_polynomialInclusion (p : Polynomial K) :
    ‖polynomialInclusion (t := t) p‖ = p.gaussNorm (NormedField.toAbsoluteValue K) t := by
  apply le_antisymm
  · apply (norm_le_iff _ (p.gaussNorm_nonneg (NormedField.toAbsoluteValue K)
      (radius_pos (t := t)).le)).mpr
    intro n
    cases n with
    | ofNat n =>
      change ‖coeff (polynomialInclusion (t := t) p) (n : ℤ)‖ * t ^ (n : ℤ) ≤ _
      simpa only [coeff_polynomialInclusion_nat, zpow_natCast,
        NormedField.toAbsoluteValue_apply] using
        p.le_gaussNorm (NormedField.toAbsoluteValue K) (radius_pos (t := t)).le n
    | negSucc n =>
      rw [coeff_polynomialInclusion_neg p (Int.negSucc_lt_zero n), norm_zero, zero_mul]
      exact p.gaussNorm_nonneg (NormedField.toAbsoluteValue K) (radius_pos (t := t)).le
  · obtain ⟨n, hn⟩ := p.exists_eq_gaussNorm (NormedField.toAbsoluteValue K) t
    rw [hn]
    simpa only [coeff_polynomialInclusion_nat, zpow_natCast,
      NormedField.toAbsoluteValue_apply] using
      norm_coeff_mul_le (polynomialInclusion (t := t) p) (n : ℤ)

/-- Translation of every Laurent exponent by `m` rescales its Gauss norm by `t^m`. -/
theorem norm_mul_monomial (p : GaussLaurent K t) (m : ℤ) :
    ‖p * single m 1‖ = ‖p‖ * t ^ m := by
  apply le_antisymm
  · simpa only [norm_single, norm_one, one_mul] using norm_mul_le p (single m 1)
  · have h : ‖p‖ ≤ ‖p * single m 1‖ / t ^ m := by
      calc
        ‖p‖ = ‖(p * single m 1) * single (-m) 1‖ := by
          rw [mul_assoc, single_mul_single, add_neg_cancel, one_mul, ← one_eq_single, mul_one]
        _ ≤ ‖p * single m 1‖ * ‖single (t := t) (-m) (1 : K)‖ := norm_mul_le _ _
        _ = ‖p * single m 1‖ / t ^ m := by
          rw [norm_single, norm_one, one_mul, zpow_neg, div_eq_mul_inv]
    exact (le_div_iff₀ (zpow_pos (radius_pos (t := t)) m)).mp h

/-- Every positive-radius Laurent Gauss norm is multiplicative, even when
several coefficients attain the maximum. -/
theorem norm_mul_general (p q : GaussLaurent K t) : ‖p * q‖ = ‖p‖ * ‖q‖ := by
  obtain ⟨n, f, hf0⟩ := LaurentPolynomial.exists_T_pow (p : LaurentPolynomial K)
  obtain ⟨m, g, hg0⟩ := LaurentPolynomial.exists_T_pow (q : LaurentPolynomial K)
  have hf : polynomialInclusion (t := t) f = p * single (t := t) (n : ℤ) 1 := hf0
  have hg : polynomialInclusion (t := t) g = q * single (t := t) (m : ℤ) 1 := hg0
  have hfg : polynomialInclusion (t := t) (f * g) =
      (p * q) * single (t := t) ((n : ℤ) + m) 1 := by
    calc
      _ = polynomialInclusion (t := t) f * polynomialInclusion (t := t) g :=
        (polynomialInclusion (t := t)).map_mul f g
      _ = (p * single (t := t) (n : ℤ) 1) *
          (q * single (t := t) (m : ℤ) 1) := by rw [hf, hg]
      _ = (p * q) * (single (t := t) (n : ℤ) 1 *
          single (t := t) (m : ℤ) 1) := by ring
      _ = _ := by rw [single_mul_single, one_mul]
  have hna : IsNonarchimedean (NormedField.toAbsoluteValue K) :=
    IsUltrametricDist.isNonarchimedean_norm
  have h := Polynomial.gaussNorm_mul hna (radius_pos (t := t)) f g
  rw [← norm_polynomialInclusion, ← norm_polynomialInclusion,
    ← norm_polynomialInclusion, hfg, hf, hg, norm_mul_monomial,
    norm_mul_monomial, norm_mul_monomial, zpow_add₀ (radius_pos (t := t)).ne'] at h
  have hw : 0 < t ^ (n : ℤ) * t ^ (m : ℤ) :=
    mul_pos (zpow_pos (radius_pos (t := t)) _) (zpow_pos (radius_pos (t := t)) _)
  apply mul_right_cancel₀ hw.ne'
  calc
    _ = ‖p‖ * t ^ (n : ℤ) * (‖q‖ * t ^ (m : ℤ)) := h
    _ = _ := by ring

end GaussLaurent

namespace CompletedGaussLaurent

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {t : ℝ} [Fact (0 < t)]

/-- Multiplicativity passes from Laurent polynomials to their completion. -/
theorem norm_mul_general (x y : CompletedGaussLaurent K t) : ‖x * y‖ = ‖x‖ * ‖y‖ := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq (continuous_norm.comp continuous_mul)
      ((continuous_norm.comp continuous_fst).mul (continuous_norm.comp continuous_snd))
  · intro p q
    rw [← UniformSpace.Completion.coe_mul, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    exact GaussLaurent.norm_mul_general p q

/-- The Gauss norm is an actual bounded multiplicative spectrum point for every
positive radius; radius independence and completeness of the coefficient field
are unnecessary. -/
def gaussPoint : BanachSpectrum (CompletedGaussLaurent K t) where
  toFun := norm
  map_zero' := norm_zero
  map_one' := norm_one'
  map_mul' := norm_mul_general
  add_le' := norm_add_le
  neg' := norm_neg
  le_norm _ := le_rfl

@[simp] theorem gaussPoint_apply (x : CompletedGaussLaurent K t) :
    gaussPoint x = ‖x‖ := rfl

end CompletedGaussLaurent

end Langlands.Analytic
