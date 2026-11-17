import Langlands.Representation.Archimedean.ComplexJacquetKernel
import Langlands.Representation.Archimedean.ComplexPartialSqCpowIntegral

/-!
# The Jacquet integral of spherical vectors

Let `χ_l(z) = (|z|²)^{e_l}` be characters of `ℂˣ` with trivial phases and strictly decreasing
`Re e_l`. A function `f` of the `U(n)`-finite principal series of `χ` with `f = 1` on `U(n)` has
`f(J(x,1) κ) = ∏_{l<m} r_{l+1}(x)^{e_{l+1} - e_l - 1}` for `κ ∈ U(m+1)` (`spherical_chart`), so
every partial Jacquet integral multiplies it by a nonzero constant, and the Jacquet integral
`Λ_n(f)` is nonzero (`jacquet_ne_zero_of_spherical`).
-/

noncomputable section

open MeasureTheory

namespace Langlands.Archimedean

set_option autoImplicit false

namespace ComplexSphericalJacquetNormalized

open ComplexMaximalParabolicIntegration ComplexParabolicChartBound ComplexPartialJacquet
  ComplexGramFormula

/-- Summation by parts with complex coefficients (as
`ComplexParabolicChartBound.sum_mul_eq_sum_sub`). -/
theorem sum_mul_eq_sum_sub {m : ℕ} {t : Fin (m + 1) → ℂ} {σ : ℕ → ℂ} {T : ℕ → ℂ}
    (hT : ∀ l : ℕ, T l = ∑ j : Fin (m + 1), if l ≤ (j : ℕ) then t j else 0) (hT0 : T 0 = 0) :
    ∑ l : Fin (m + 1), σ l * t l = ∑ l : Fin m, (σ ((l : ℕ) + 1) - σ l) * T ((l : ℕ) + 1) := by
  have hTlast : T (m + 1) = 0 := by
    rw [hT]
    exact Finset.sum_eq_zero fun j _ => ite_eq_right (by omega)
  have ht : ∀ l : Fin (m + 1), t l = T l - T ((l : ℕ) + 1) := by
    intro l
    rw [hT, hT, ← Finset.sum_sub_distrib]
    have h : ∀ j : Fin (m + 1), ((if (l : ℕ) ≤ (j : ℕ) then t j else 0) -
        if (l : ℕ) + 1 ≤ (j : ℕ) then t j else 0) = if j = l then t j else 0 := by
      intro j
      by_cases hj : j = l
      · subst hj
        rw [ite_eq_left le_rfl, ite_eq_right (by omega), ite_eq_left rfl, sub_zero]
      · rw [ite_eq_right hj]
        have hjv : (j : ℕ) ≠ (l : ℕ) := fun h => hj (Fin.ext h)
        by_cases hlj : (l : ℕ) ≤ (j : ℕ)
        · rw [ite_eq_left hlj, ite_eq_left (by omega), sub_self]
        · rw [ite_eq_right hlj, ite_eq_right (by omega), sub_self]
    rw [Finset.sum_congr rfl fun j _ => h j, Finset.sum_ite_eq']
    simp
  calc ∑ l : Fin (m + 1), σ l * t l
      = ∑ l : Fin (m + 1), σ l * T l - ∑ l : Fin (m + 1), σ l * T ((l : ℕ) + 1) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by rw [ht l]; ring
    _ = ∑ l : Fin m, (σ ((l : ℕ) + 1) - σ l) * T ((l : ℕ) + 1) := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
        simp only [Fin.val_zero, hT0, mul_zero, zero_add, Fin.val_succ, Fin.val_castSucc,
          Fin.val_last, hTlast, add_zero]
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring

theorem ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (s : ℂ) :
    ((r : ℝ) : ℂ) ^ s = Complex.exp (s * (Real.log r : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'), Complex.ofReal_log hr.le, mul_comm]

variable {m : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- The exponents `e_{l+1} - e_l - 1` of the chart values of spherical vectors. -/
def chartExp (e : ℕ → ℂ) (m : ℕ) : Fin m → ℂ := fun l => e ((l : ℕ) + 1) - e l - 1

/-- **Spherical vectors on the chart.** If `f` is in the principal series of `χ`, `χ` has trivial
phases and `f = 1` on `U(m+1)`, then `f(J(x,1) κ) = ∏_{l<m} r_{l+1}(x)^{e_{l+1} - e_l - 1}` for
`κ ∈ U(m+1)`. -/
theorem spherical_chart (hχ : IsPhasePower χ e) (hph : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = 1)
    {f : Langlands.GeneralLinear (m + 1) ℂ → ℂ} (hf : f ∈ principalSeries ℂ (m + 1) χ)
    (hf1 : ∀ k ∈ unitaryCompact ℂ (m + 1), f k = 1) (x : Fin m → ℂ)
    {κ : Langlands.GeneralLinear (m + 1) ℂ} (hκ : κ ∈ unitaryCompact ℂ (m + 1)) :
    f (chartGL x * κ) = ComplexPartialSqCpow.integrand m (chartExp e m) 0 x := by
  obtain ⟨a, u, k, hk, hg⟩ :=
    ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary (chartGL x * κ)
  rw [hg, hf.2 a u k, hf1 k hk, mul_one]
  have ha : ∀ i, 0 < ‖(a i : ℂ)‖ := fun i => norm_pos_iff.mpr (a i).ne_zero
  set t : Fin (m + 1) → ℂ := fun i => ((2 * Real.log ‖(a i : ℂ)‖ : ℝ) : ℂ) with htdef
  set T : ℕ → ℂ := fun l => ∑ j : Fin (m + 1), if l ≤ (j : ℕ) then t j else 0 with hTdef
  set s : ℕ → ℂ := fun i => e i + (((m + 1 : ℕ) : ℂ) - 1) / 2 - (i : ℂ) with hsdef
  have hTval : ∀ l : ℕ, l ≤ m → T l = (Real.log (partialSq x l) : ℂ) := by
    intro l hl
    rw [← prod_tail_sq_eq x κ hκ a u k hk hg hl, Real.log_pow, norm_prod,
      Real.log_prod (fun j _ => by
        split_ifs
        · exact (ha j).ne'
        · simp)]
    simp only [hTdef, htdef]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hT0 : T 0 = 0 := by
    rw [hTval 0 (Nat.zero_le _), partialSq_zero, Real.log_one, Complex.ofReal_zero]
  -- the character as an exponential
  have hL : principalSeriesCharacter ℂ (m + 1) χ a =
      Complex.exp (∑ i : Fin (m + 1), s i * t i) := by
    rw [principalSeriesCharacter, Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hχ.eq i (a i), hph, one_mul, Complex.finrank_real_complex]
    have hr : 0 < ‖(a i : ℂ)‖ ^ 2 := pow_pos (ha i) 2
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hr.ne'), ofReal_cpow_eq_exp hr, Real.log_pow]
    simp only [hsdef, htdef]
    push_cast
    ring_nf
  -- the chart integrand as an exponential
  have hR : ComplexPartialSqCpow.integrand m (chartExp e m) 0 x =
      Complex.exp (∑ l : Fin m, (s ((l : ℕ) + 1) - s l) * T ((l : ℕ) + 1)) := by
    rw [ComplexPartialSqCpow.integrand, Complex.cpow_zero, one_mul, Complex.exp_sum]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [ofReal_cpow_eq_exp (partialSq_pos x _), hTval _ (by have := l.isLt; omega)]
    congr 1
    simp only [chartExp, hsdef]
    push_cast
    ring
  rw [hL, hR, sum_mul_eq_sum_sub (fun l => rfl) hT0]

/-- **The Jacquet integral of a spherical vector is nonzero.** -/
theorem jacquet_ne_zero_of_spherical : ∀ (n : ℕ) (χ : ℕ → ℂˣ → ℂ) (e : ℕ → ℂ),
    IsPhasePower χ e → (∀ l : ℕ, l + 1 < n → (e (l + 1)).re < (e l).re) →
    (∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = 1) →
    ∀ f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n),
      (∀ k ∈ unitaryCompact ℂ n, f k = 1) → ComplexJacquetDual.jacquet n f ≠ 0
  | 0, _, _, _, _, _, f, _, hf1 => by
      show f 1 ≠ 0
      rw [hf1 1 (one_mem _)]
      exact one_ne_zero
  | m + 1, χ, e, hχ, hdom, hph, f, hf, hf1 => by
      have he : IsStrictlyDominant e m := fun l hl => hdom l (by omega)
      have hstep := jacquetStep_mem hχ he hf
      set C := ∫ x, ComplexPartialSqCpow.integrand m (chartExp e m) 0 x with hCdef
      have hC : C ≠ 0 := ComplexPartialSqCpow.integral_integrand_ne_zero m (chartExp e m) 0
        (fun l => by
          have := hdom l (by omega)
          simp only [chartExp, Complex.sub_re, Complex.one_re]
          linarith)
        (by simp)
      have hval : ∀ k ∈ unitaryCompact ℂ m, jacquetStep f k = C := by
        intro k hk
        simp only [jacquetStep, hCdef]
        congr 1
        funext x
        exact spherical_chart hχ hph hf.1 hf1 x (iotaGL_mem_unitaryCompact hk)
      set g := C⁻¹ • jacquetStep f with hgdef
      have hg : g ∈ kFiniteFunctions (principalSeries ℂ m (shiftChar χ)) (unitaryCompact ℂ m) :=
        Submodule.smul_mem _ _ hstep
      have hg1 : ∀ k ∈ unitaryCompact ℂ m, g k = 1 := by
        intro k hk
        simp only [hgdef, Pi.smul_apply, smul_eq_mul, hval k hk, inv_mul_cancel₀ hC]
      have hIH := jacquet_ne_zero_of_spherical m (shiftChar χ) (fun l => e l - 1 / 2) hχ.shift
        (fun l hl => by
          have := hdom l (by omega)
          simp only [Complex.sub_re]
          linarith)
        (fun l z => by
          simp [shiftChar, hph, norm_phaseUnit])
        g hg hg1
      have hfg : jacquetStep f = C • g := by
        rw [hgdef, smul_smul, mul_inv_cancel₀ hC, one_smul]
      show ComplexJacquetDual.jacquet m (jacquetStep f) ≠ 0
      rw [hfg, ComplexJacquetKernel.jacquet_smul]
      exact mul_ne_zero hC hIH

end ComplexSphericalJacquetNormalized

end Langlands.Archimedean
