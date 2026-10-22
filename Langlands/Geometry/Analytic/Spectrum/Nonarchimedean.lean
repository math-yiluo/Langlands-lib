import Langlands.Geometry.Analytic.Spectrum.Properties
import Langlands.Geometry.Analytic.Spectrum.Nonarchimedean.Statement

/-! # Strong triangle inequality of actual spectrum seminorms -/

noncomputable section

universe u v

namespace Langlands.Analytic

private theorem seminorm_sum_le {A : Type*} [CommRing A]
    (p : MulRingSeminorm A) {ι : Type*} (s : Finset ι) (f : ι → A) :
    p (∑ i ∈ s, f i) ≤ ∑ i ∈ s, p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi hs =>
      simp only [Finset.sum_insert hi]
      exact (map_add_le_add p _ _).trans (add_le_add le_rfl hs)

/-- A multiplicative seminorm bounded by one on natural numbers is
nonarchimedean. The proof uses binomial expansion and exponential growth. -/
theorem seminorm_nonarchimedean_of_natCast {A : Type*} [CommRing A]
    (p : MulRingSeminorm A) (hnat : ∀ n : ℕ, p (n : A) ≤ 1) :
    IsNonarchimedean p := by
  intro a b
  let M := max (p a) (p b)
  have hM : 0 ≤ M := (apply_nonneg p a).trans (le_max_left _ _)
  have hpow (n : ℕ) : p (a + b) ^ n ≤ (n + 1 : ℝ) * M ^ n := by
    rw [← map_pow, add_pow]
    refine (seminorm_sum_le p _ _).trans ?_
    calc
      ∑ i ∈ Finset.range (n + 1), p (a ^ i * b ^ (n - i) * (n.choose i : A))
          ≤ ∑ _i ∈ Finset.range (n + 1), M ^ n := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        rw [map_mul, map_mul, map_pow, map_pow]
        calc
          p a ^ i * p b ^ (n - i) * p (n.choose i : A)
              ≤ (M ^ i * M ^ (n - i)) * 1 := by
                gcongr
                · exact le_max_left _ _
                · exact le_max_right _ _
                · exact hnat _
          _ = M ^ n := by rw [mul_one, ← pow_add, Nat.add_sub_of_le hin]
      _ = (n + 1 : ℝ) * M ^ n := by simp
  rcases hM.eq_or_lt with hzero | hpos
  · have h := hpow 1
    exact (by simpa only [← hzero, pow_one, mul_zero] using h :
      p (a + b) ≤ 0).trans hM
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  obtain ⟨n, hn⟩ := Real.exists_natCast_add_one_lt_pow_of_one_lt
    ((one_lt_div hpos).mpr hr)
  rw [div_pow, lt_div_iff₀ (pow_pos hpos n)] at hn
  have hn0 : n ≠ 0 := by
    intro hn0
    simp [hn0] at hn
  exact le_of_pow_le_pow_left₀ hn0 (hpos.trans hr).le ((hpow n).trans hn.le)

namespace BanachSpectrum

variable {A : Type u} [NormedCommRing A]
  {K : Type v} [NormedField K] [IsUltrametricDist K] [NormedAlgebra K A]

include K in
/-- Spectrum seminorms over an ultrametric field satisfy the strong triangle
inequality; this is derived, not an additional field of the spectrum. -/
theorem isNonarchimedean (x : BanachSpectrum A) :
    IsNonarchimedean x.toMulRingSeminorm := by
  apply seminorm_nonarchimedean_of_natCast
  intro n
  have h := algebraMap_apply (K := K) x (n : K)
  rw [map_natCast] at h
  exact h.trans_le (IsUltrametricDist.norm_natCast_le_one K n)


end BanachSpectrum

/-- Natural-number boundedness and scalar normalization give the strong
triangle inequality for actual multiplicative seminorms. -/
theorem spectrumNonarchimedean : SpectrumNonarchimedeanStatement.{u, v} := by
  constructor
  · intro A _ p hnat
    exact seminorm_nonarchimedean_of_natCast p hnat
  · intro A K _ _ _ _ x
    exact x.isNonarchimedean (K := K)

end Langlands.Analytic
