import Langlands.Geometry.Analytic.GeneralizedAffinoid.GaussLaurentRationalDecomposition
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormStabilizer

/-! # Finite rational pullback under the relative Laurent Gauss section -/

noncomputable section

universe u v

namespace Langlands.Analytic.RelativeLaurentAnnulus

open PresentedAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

private theorem spectrum_apply_eq_of_norm_sub_lt {B : Type v}
    [NormedCommRing B] [NormedAlgebra K B] (x : BanachSpectrum B) (a b : B)
    (h : ‖a - b‖ < x b) : x a = x b := by
  have hsmall : x.toMulRingSeminorm (a - b) < x.toMulRingSeminorm b :=
    (x.le_norm _).trans_lt h
  simpa only [sub_add_cancel] using
    (x.isNonarchimedean (K := K)).add_eq_right_of_lt
      (map_neg_eq_map x.toMulRingSeminorm) hsmall

private theorem spectrum_le_iff_of_norm_sub_lt {B : Type v}
    [NormedCommRing B] [NormedAlgebra K B] (x : BanachSpectrum B) (a b : B)
    (c : ℝ) (h : ‖a - b‖ < c) : x a ≤ c ↔ x b ≤ c := by
  constructor
  · intro ha
    have hba : x.toMulRingSeminorm (b - a) ≤ c := by
      apply (x.le_norm _).trans
      rw [norm_sub_rev]
      exact h.le
    simpa only [sub_add_cancel] using
      (x.isNonarchimedean (K := K) (b - a) a).trans (max_le hba ha)
  · intro hb
    have hab : x.toMulRingSeminorm (a - b) ≤ c := (x.le_norm _).trans h.le
    simpa only [sub_add_cancel] using
      (x.isNonarchimedean (K := K) (a - b) b).trans (max_le hab hb)

variable [CompleteSpace K] (t : ℝ) [Fact (0 < t)]
  {A : PresentedAffinoidAlgebra K}

/-- Uniform finite Laurent approximation preserves rational inequalities exactly
above a fixed positive denominator threshold. -/
theorem exists_polynomial_ratio_approximation {I : Type v} [Fintype I]
    (f : I → algebra K A t) (g : algebra K A t)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (q : ℝ) (hq : 0 < q) :
    ∃ (fp : I → AddMonoidAlgebra A ℤ) (gp : AddMonoidAlgebra A ℤ),
      ∀ x : BanachSpectrum A,
        (q ≤ sectionPoint K A t x g ∧
          ∀ i, sectionPoint K A t x (f i) ≤ r i * sectionPoint K A t x g) ↔
        (q ≤ sectionPoint K A t x (polynomialMap K A t gp) ∧
          ∀ i, sectionPoint K A t x (polynomialMap K A t (fp i)) ≤
            r i * sectionPoint K A t x (polynomialMap K A t gp)) := by
  classical
  obtain ⟨gp, hgp⟩ := (denseRange_polynomialMap K A t).exists_dist_lt g hq
  have hfp : ∀ i, ∃ p : AddMonoidAlgebra A ℤ,
      dist (f i) (polynomialMap K A t p) < r i * q :=
    fun i => (denseRange_polynomialMap K A t).exists_dist_lt (f i) (mul_pos (hr i) hq)
  choose fp hfp using hfp
  rw [dist_eq_norm] at hgp
  simp only [dist_eq_norm] at hfp
  refine ⟨fp, gp, fun x => ?_⟩
  have heq (hx : q ≤ sectionPoint K A t x g) :
      sectionPoint K A t x (polynomialMap K A t gp) = sectionPoint K A t x g := by
    apply spectrum_apply_eq_of_norm_sub_lt K
    rw [norm_sub_rev]
    exact hgp.trans_le hx
  have heq' (hx : q ≤ sectionPoint K A t x (polynomialMap K A t gp)) :
      sectionPoint K A t x g = sectionPoint K A t x (polynomialMap K A t gp) :=
    spectrum_apply_eq_of_norm_sub_lt K _ _ _ (hgp.trans_le hx)
  constructor
  · rintro ⟨hx, hf⟩
    have hg := heq hx
    refine ⟨by rwa [hg], fun i => ?_⟩
    rw [hg]
    exact (spectrum_le_iff_of_norm_sub_lt K (sectionPoint K A t x) _ _ _
      ((hfp i).trans_le (mul_le_mul_of_nonneg_left hx (hr i).le))).mp (hf i)
  · rintro ⟨hx, hf⟩
    have hg := heq' hx
    refine ⟨by rwa [hg], fun i => ?_⟩
    rw [hg]
    exact (spectrum_le_iff_of_norm_sub_lt K (sectionPoint K A t x) _ _ _
      ((hfp i).trans_le (mul_le_mul_of_nonneg_left hx (hr i).le))).mpr (hf i)

/-- Arbitrary actual Laurent quotient data with a positive threshold have a
finite decomposition by actual rational charts over the original algebra. -/
theorem exists_finite_ratio_charts {I : Type v} [Fintype I]
    (f : I → algebra K A t) (g : algebra K A t)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (q : ℝ) (hq : 0 < q) :
    ∃ (m : ℕ) (D : Fin m → RationalChart K A), ∀ x : BanachSpectrum A,
      (q ≤ sectionPoint K A t x g ∧
        ∀ i, sectionPoint K A t x (f i) ≤ r i * sectionPoint K A t x g) ↔
        ∃ j, x ∈ (D j).locus := by
  obtain ⟨fp, gp, happrox⟩ :=
    exists_polynomial_ratio_approximation K t f g r hr q hq
  obtain ⟨m, D, hD⟩ :=
    exists_finite_polynomial_ratio_charts K t fp gp r hr q hq
  exact ⟨m, D, fun x => (happrox x).trans (hD x)⟩

/-- Every actual rational chart on the relative Laurent annulus pulls back to a
finite union of actual rational charts on the original affinoid algebra. -/
theorem exists_finite_rational_pullback (d : RationalChart K (algebra K A t)) :
    ∃ (m : ℕ) (D : Fin m → RationalChart K A), ∀ x : BanachSpectrum A,
      sectionPoint K A t x ∈ d.locus ↔ ∃ j, x ∈ (D j).locus := by
  obtain ⟨q, hq, hbound⟩ := d.exists_pos_le_denominator
  obtain ⟨m, D, hD⟩ := exists_finite_ratio_charts K t d.numeratorClass
    d.denominatorClass d.radii d.radii.positive q hq
  refine ⟨m, D, fun x => ?_⟩
  rw [← hD x]
  constructor
  · intro hx
    exact ⟨hbound _ hx, hx⟩
  · exact And.right

/-- Chosen finite ambient charts for the pullback of an actual annulus rational chart. -/
def rationalPullbackCharts (d : RationalChart K (algebra K A t)) :
    Σ m : ℕ, Fin m → RationalChart K A :=
  ⟨(exists_finite_rational_pullback K t d).choose,
    (exists_finite_rational_pullback K t d).choose_spec.choose⟩

@[simp] theorem mem_rationalPullbackCharts (d : RationalChart K (algebra K A t))
    (x : BanachSpectrum A) :
    sectionPoint K A t x ∈ d.locus ↔
      ∃ j, x ∈ ((rationalPullbackCharts K t d).2 j).locus :=
  (exists_finite_rational_pullback K t d).choose_spec.choose_spec x

theorem preimage_gaussSection_rational_locus
    (d : RationalChart K (algebra K A t)) :
    gaussSection K A t ⁻¹' d.locus =
      ⋃ j, ((rationalPullbackCharts K t d).2 j).locus := by
  ext x
  simpa only [Set.mem_preimage, gaussSection_apply, Set.mem_iUnion] using
    mem_rationalPullbackCharts K t d x

end Langlands.Analytic.RelativeLaurentAnnulus
