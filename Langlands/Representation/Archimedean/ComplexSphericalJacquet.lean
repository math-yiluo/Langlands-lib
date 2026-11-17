import Langlands.Representation.Archimedean.ComplexStrictLanglandsQuotient
import Langlands.Representation.Archimedean.ComplexPartialSqIntegral
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Jacquet integral of the spherical vector

For phase-power characters `χ` with exponents `e` that are trivial on phases and have strictly
decreasing real parts, a principal-series function `T` constant on `U(n)` with `T 1 ≠ 0` has
nonzero Jacquet integral `ComplexJacquetDual.jacquet n T` (`ComplexSphericalJacquet.jacquet_ne_zero`).

* Along the chart, `T(J(x,1)) = T(1) ∏_{l<m} r_{l+1}(x)^{e_{l+1}-e_l-1}` with
  `r_l(x) = 1 + ∑_{j<l} |x_j|²` (`apply_chartGL`, by the Iwasawa decomposition of `J(x,1)` and
  summation by parts).
* `∫_ℂ (A + |y|²)^σ dy = -π A^{σ+1}/(σ+1)` (`integral_add_norm_sq_cpow`), so the iterated
  integral of `∏ r_{l+1}^{s_l}` is a product of nonzero factors (`integral_chartFun_ne_zero`).
* Induction on `n` through `ComplexPartialJacquet.jacquetStep`.

Consequence: `ComplexSphericalCyclicStatement`, proved as `complexSphericalCyclic`: for weight-zero
characters with strictly decreasing real parts of the exponents, every `(𝔤𝔩_n(ℂ), U(n))`-submodule
of the standard module containing the spherical vector is everything, because proper submodules
lie in the kernel of the Jacquet integral (`ComplexJacquetKernel.jacquet_eq_zero_of_proper`).
-/

noncomputable section

open MeasureTheory Set

open scoped Manifold ContDiff Matrix.Norms.Operator ComplexConjugate TensorProduct

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexSphericalJacquet

open ComplexParabolicChartBound ComplexPartialSqIntegral

/-! ## The rank-one integral -/

theorem preimage_add_Ioi (A : ℝ) : (fun t : ℝ => A + t) ⁻¹' Ioi A = Ioi 0 := by
  ext t
  simp

/-- `∫_ℂ (A + |y|²)^σ dy = -π A^(σ+1) / (σ+1)` for `A > 0` and `Re σ < -1`. -/
theorem integral_add_norm_sq_cpow {A : ℝ} (hA : 0 < A) {σ : ℂ} (hσ : σ.re < -1) :
    ∫ y : ℂ, (((A + ‖y‖ ^ 2 : ℝ)) : ℂ) ^ σ = -(Real.pi : ℂ) * (A : ℂ) ^ (σ + 1) / (σ + 1) := by
  have h1 := integral_fun_norm_addHaar (volume : Measure ℂ)
    (fun r : ℝ => (((A + r ^ 2 : ℝ)) : ℂ) ^ σ)
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real]
  rw [Complex.finrank_real_complex, hball] at h1
  have h2 := integral_comp_rpow_Ioi_of_pos (g := fun t : ℝ => (((A + t : ℝ)) : ℂ) ^ σ)
    (p := 2) two_pos
  have h3 : ∫ t in Ioi (0 : ℝ), (((A + t : ℝ)) : ℂ) ^ σ = ∫ u in Ioi A, (u : ℂ) ^ σ := by
    have := (measurePreserving_add_left (volume : Measure ℝ) A).setIntegral_preimage_emb
      (measurableEmbedding_addLeft A) (fun u : ℝ => (u : ℂ) ^ σ) (Ioi A)
    rw [preimage_add_Ioi] at this
    simpa using this
  have h4 := integral_Ioi_cpow_of_lt hσ hA
  have h5 : ∫ x in Ioi (0 : ℝ), (2 * x ^ ((2 : ℝ) - 1)) • (((A + x ^ (2 : ℝ) : ℝ)) : ℂ) ^ σ =
      (2 : ℝ) • ∫ x in Ioi (0 : ℝ), x ^ (2 - 1 : ℕ) • (((A + x ^ 2 : ℝ)) : ℂ) ^ σ := by
    rw [← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, smul_smul]
    simp
  beta_reduce at h1 h2
  have hJ : (2 : ℝ) • ∫ x in Ioi (0 : ℝ), x ^ (2 - 1 : ℕ) • (((A + x ^ 2 : ℝ)) : ℂ) ^ σ =
      -(A : ℂ) ^ (σ + 1) / (σ + 1) := by
    rw [← h5, h2, h3, h4]
  have hJ' : (2 : ℕ) • ∫ x in Ioi (0 : ℝ), x ^ (2 - 1 : ℕ) • (((A + x ^ 2 : ℝ)) : ℂ) ^ σ =
      -(A : ℂ) ^ (σ + 1) / (σ + 1) := by
    rw [← hJ, ← Nat.cast_smul_eq_nsmul ℝ]
    norm_num
  rw [h1, smul_comm, hJ', Complex.real_smul]
  ring


/-! ## The iterated chart integral -/

/-- `y ↦ r_m(y)^w ∏_{l<m} r_{l+1}(y)^{s_l}` on `ℂ^m`, with complex exponents. -/
def chartFun (m : ℕ) (s : Fin m → ℂ) (w : ℂ) (y : Fin m → ℂ) : ℂ :=
  ((partialSq y m : ℝ) : ℂ) ^ w * ∏ l : Fin m, ((partialSq y ((l : ℕ) + 1) : ℝ) : ℂ) ^ s l

variable {m : ℕ}

theorem norm_chartFun (s : Fin m → ℂ) (w : ℂ) (y : Fin m → ℂ) :
    ‖chartFun m s w y‖ =
      partialSq y m ^ w.re * ∏ l : Fin m, partialSq y ((l : ℕ) + 1) ^ (s l).re := by
  rw [chartFun, norm_mul, norm_prod, Complex.norm_cpow_eq_rpow_re_of_pos (partialSq_pos y m)]
  congr 1
  exact Finset.prod_congr rfl fun l _ =>
    Complex.norm_cpow_eq_rpow_re_of_pos (partialSq_pos y _) _

theorem measurable_chartFun (s : Fin m → ℂ) (w : ℂ) : Measurable (chartFun m s w) :=
  ((Complex.measurable_ofReal.comp (continuous_partialSq m).measurable).pow_const w).mul
    (Finset.measurable_prod _ fun _ _ =>
      (Complex.measurable_ofReal.comp (continuous_partialSq _).measurable).pow_const _)

theorem integrable_chartFun {s : Fin m → ℂ} {w : ℂ}
    (h : TailCondition (fun l => (s l).re) w.re) : Integrable (chartFun m s w) :=
  (integrable_partialSq_mul_prod m _ _ h).mono' (measurable_chartFun s w).aestronglyMeasurable
    (ae_of_all _ fun y => (norm_chartFun s w y).le)

theorem chartFun_snoc (s : Fin (m + 1) → ℂ) (w : ℂ) (y : Fin m → ℂ) (t : ℂ) :
    chartFun (m + 1) s w (Fin.snoc y t) =
      (((partialSq y m + ‖t‖ ^ 2 : ℝ)) : ℂ) ^ (w + s (Fin.last m)) *
        ∏ l : Fin m, ((partialSq y ((l : ℕ) + 1) : ℝ) : ℂ) ^ s (Fin.castSucc l) := by
  unfold chartFun
  rw [Fin.prod_univ_castSucc]
  simp only [partialSq_snoc_castSucc, Fin.val_castSucc, Fin.val_last]
  rw [partialSq_snoc_last]
  have hne : (((partialSq y m + ‖t‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by
    have := partialSq_pos y m
    exact_mod_cast (by positivity : (0 : ℝ) < partialSq y m + ‖t‖ ^ 2).ne'
  rw [Complex.cpow_add _ _ hne]
  ring

theorem tail_last {s : Fin (m + 1) → ℂ} {w : ℂ} (h : TailCondition (fun l => (s l).re) w.re) :
    (w + s (Fin.last m)).re < -1 := by
  have := h (Fin.last m)
  have hsum : (∑ l : Fin (m + 1), (if Fin.last m ≤ l then (s l).re + 1 else 0)) =
      (s (Fin.last m)).re + 1 := by
    rw [Fin.sum_univ_castSucc]
    simp
  rw [hsum] at this
  rw [Complex.add_re]
  linarith

theorem tail_castSucc {s : Fin (m + 1) → ℂ} {w : ℂ}
    (h : TailCondition (fun l => (s l).re) w.re) :
    TailCondition (fun l : Fin m => (s (Fin.castSucc l)).re) (w + s (Fin.last m) + 1).re := by
  intro j
  have := h (Fin.castSucc j)
  rw [Fin.sum_univ_castSucc] at this
  simp only [Fin.castSucc_le_castSucc_iff, Fin.le_last, ite_true] at this
  simp only [Complex.add_re, Complex.one_re]
  linarith

theorem integral_chartFun_succ {s : Fin (m + 1) → ℂ} {w : ℂ}
    (h : TailCondition (fun l => (s l).re) w.re) :
    ∫ x, chartFun (m + 1) s w x =
      (-(Real.pi : ℂ) / (w + s (Fin.last m) + 1)) *
        ∫ y, chartFun m (fun l => s (Fin.castSucc l)) (w + s (Fin.last m) + 1) y := by
  set σ : ℂ := w + s (Fin.last m) with hσdef
  have hσ : σ.re < -1 := tail_last h
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) (Fin.last m)
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) (Fin.last m)
  set G : ℂ × (Fin m → ℂ) → ℂ := fun p =>
    (((partialSq p.2 m + ‖p.1‖ ^ 2 : ℝ)) : ℂ) ^ σ *
      ∏ l : Fin m, ((partialSq p.2 ((l : ℕ) + 1) : ℝ) : ℂ) ^ s (Fin.castSucc l) with hGdef
  have key : chartFun (m + 1) s w ∘ e.symm = G := by
    funext p
    obtain ⟨t, y⟩ := p
    simp only [Function.comp_apply, e, MeasurableEquiv.piFinSuccAbove_symm_apply, hGdef]
    have hx : (Fin.insertNthEquiv (fun _ : Fin (m + 1) => ℂ) (Fin.last m)) (t, y) =
        (Fin.snoc y t : Fin (m + 1) → ℂ) := Fin.insertNth_last' _ _
    rw [hx, chartFun_snoc]
  have hint : Integrable G (volume.prod volume) := by
    rw [← key, ← Measure.volume_eq_prod]
    exact (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr (integrable_chartFun h)
  have h1 : ∫ x, chartFun (m + 1) s w x = ∫ p, G p ∂(volume.prod volume) := by
    rw [← key, ← Measure.volume_eq_prod]
    exact (hmp.symm.integral_comp' (chartFun (m + 1) s w)).symm
  rw [h1, integral_prod_symm G hint, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [hGdef]
  rw [integral_mul_const, integral_add_norm_sq_cpow (partialSq_pos y m) hσ, chartFun]
  ring

theorem integral_chartFun_ne_zero : ∀ (m : ℕ) (s : Fin m → ℂ) (w : ℂ),
    TailCondition (fun l => (s l).re) w.re → ∫ y, chartFun m s w y ≠ 0
  | 0, s, w, _ => by
      have h1 : ∀ y : Fin 0 → ℂ, chartFun 0 s w y = 1 := fun y => by
        simp [chartFun, partialSq_zero]
      rw [integral_congr_ae (ae_of_all _ h1), integral_const, Complex.real_smul, mul_one,
        Complex.ofReal_ne_zero, Measure.real, volume_pi, Measure.pi_univ]
      simp
  | m + 1, s, w, h => by
      rw [integral_chartFun_succ h]
      have hσ := tail_last h
      refine mul_ne_zero (div_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
        Real.pi_ne_zero)) fun h0 => ?_) (integral_chartFun_ne_zero m _ _ (tail_castSucc h))
      have := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
      rw [Complex.add_re] at hσ
      linarith

/-! ## The spherical vector along the chart -/

section Chart

open ComplexMaximalParabolicIntegration ComplexPartialJacquet ComplexGramFormula
  Langlands.GeneralLinear

variable {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-- Summation by parts with complex coefficients. -/
theorem sum_mul_eq_sum_sub_complex {t : Fin (m + 1) → ℂ} {σ : ℕ → ℂ} {T : ℕ → ℂ}
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

theorem ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ((r : ℝ) : ℂ) ^ z = Complex.exp ((Real.log r : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'), Complex.ofReal_log hr.le]

/-- The principal-series character of the diagonal part of the Iwasawa decomposition of
`J(x, 1)`, for characters trivial on phases. -/
theorem principalSeriesCharacter_chart (hχ : IsPhasePower χ e)
    (h0 : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = 1) (x : Fin m → ℂ)
    (a : Fin (m + 1) → ℂˣ) (u : upperUnipotent (m + 1) ℂ)
    (k : Langlands.GeneralLinear (m + 1) ℂ) (hk : k ∈ unitaryCompact ℂ (m + 1))
    (hg : chartGL x = (Iwasawa.diagonalUnits a : Langlands.GeneralLinear (m + 1) ℂ) *
      (u : Langlands.GeneralLinear (m + 1) ℂ) * k) :
    principalSeriesCharacter ℂ (m + 1) χ a =
      ∏ l : Fin m, ((partialSq x ((l : ℕ) + 1) : ℝ) : ℂ) ^ (e ((l : ℕ) + 1) - e l - 1) := by
  have ha : ∀ l, 0 < ‖(a l : ℂ)‖ := fun l => norm_pos_iff.mpr (a l).ne_zero
  set t : Fin (m + 1) → ℂ := fun j => ((2 * Real.log ‖(a j : ℂ)‖ : ℝ) : ℂ) with htdef
  set σ : ℕ → ℂ := fun i => e i + (((m + 1 : ℕ) : ℂ) - 1) / 2 - (i : ℂ) with hσdef
  set T : ℕ → ℂ := fun l => ∑ j : Fin (m + 1), if l ≤ (j : ℕ) then t j else 0 with hTdef
  have hT : ∀ l : ℕ, l ≤ m → T l = (Real.log (partialSq x l) : ℂ) := by
    intro l hl
    have h := prod_tail_sq_eq x 1 (unitaryCompact ℂ (m + 1)).one_mem a u k hk
      (by rw [mul_one]; exact hg) hl
    rw [← h, Real.log_pow, norm_prod, Real.log_prod]
    · rw [hTdef]
      simp only [htdef]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    · intro j _
      split_ifs
      · exact (ha j).ne'
      · simp
  have hT0 : T 0 = 0 := by
    rw [hT 0 (Nat.zero_le _), partialSq_zero, Real.log_one, Complex.ofReal_zero]
  have hsum := sum_mul_eq_sum_sub_complex (t := t) (σ := σ) (T := T) (fun l => rfl) hT0
  have hlhs : principalSeriesCharacter ℂ (m + 1) χ a =
      Complex.exp (∑ l : Fin (m + 1), σ l * t l) := by
    rw [Complex.exp_sum, principalSeriesCharacter]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hpos : (0 : ℝ) < ‖(a i : ℂ)‖ ^ 2 := pow_pos (ha i) 2
    rw [hχ.eq, h0, one_mul, Complex.finrank_real_complex,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hpos.ne'), ofReal_cpow_eq_exp hpos,
      Real.log_pow]
    congr 1
    simp only [htdef, hσdef]
    push_cast
    ring
  have hrhs : ∏ l : Fin m, ((partialSq x ((l : ℕ) + 1) : ℝ) : ℂ) ^ (e ((l : ℕ) + 1) - e l - 1) =
      Complex.exp (∑ l : Fin m, (σ ((l : ℕ) + 1) - σ l) * T ((l : ℕ) + 1)) := by
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [ofReal_cpow_eq_exp (partialSq_pos x _), hT _ (by have := l.isLt; omega)]
    congr 1
    simp only [hσdef]
    push_cast
    ring
  rw [hlhs, hsum, hrhs]

/-- Right `U(n)`-invariance of a principal-series function that is constant on `U(n)`. -/
theorem apply_mul_unitary {n : ℕ} {T : Langlands.GeneralLinear n ℂ → ℂ}
    (hT : T ∈ principalSeries ℂ n χ) (hK : ∀ k ∈ unitaryCompact ℂ n, T k = T 1)
    (g : Langlands.GeneralLinear n ℂ) {κ : Langlands.GeneralLinear n ℂ}
    (hκ : κ ∈ unitaryCompact ℂ n) : T (g * κ) = T g := by
  obtain ⟨a, u, k, hk, hg⟩ :=
    ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  rw [hg, mul_assoc _ k κ, hT.2 a u (k * κ), hT.2 a u k, hK _ (mul_mem hk hκ), hK k hk]

variable {T : Langlands.GeneralLinear (m + 1) ℂ → ℂ}

/-- **The spherical vector along the chart.** `T(J(x,1)) = T(1) ∏_{l<m} r_{l+1}(x)^{e_{l+1}-e_l-1}`. -/
theorem apply_chartGL (hχ : IsPhasePower χ e) (h0 : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = 1)
    (hT : T ∈ principalSeries ℂ (m + 1) χ) (hK : ∀ k ∈ unitaryCompact ℂ (m + 1), T k = T 1)
    (x : Fin m → ℂ) :
    T (chartGL x) = T 1 * chartFun m (fun l => e ((l : ℕ) + 1) - e l - 1) 0 x := by
  obtain ⟨a, u, k, hk, hg⟩ :=
    ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary (chartGL x)
  rw [hg, hT.2 a u k, hK k hk, principalSeriesCharacter_chart hχ h0 x a u k hk hg, chartFun,
    Complex.cpow_zero, one_mul, mul_comm]

theorem jacquetStep_unitary (hT : T ∈ principalSeries ℂ (m + 1) χ)
    (hK : ∀ k ∈ unitaryCompact ℂ (m + 1), T k = T 1) {k : Langlands.GeneralLinear m ℂ}
    (hk : k ∈ unitaryCompact ℂ m) : jacquetStep T k = jacquetStep T 1 := by
  unfold jacquetStep
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [map_one, mul_one]
  exact apply_mul_unitary hT hK _ (iotaGL_mem_unitaryCompact hk)

theorem jacquetStep_one (hχ : IsPhasePower χ e) (h0 : ∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = 1)
    (hT : T ∈ principalSeries ℂ (m + 1) χ) (hK : ∀ k ∈ unitaryCompact ℂ (m + 1), T k = T 1) :
    jacquetStep T 1 = T 1 * ∫ x, chartFun m (fun l => e ((l : ℕ) + 1) - e l - 1) 0 x := by
  unfold jacquetStep
  simp only [map_one, mul_one]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun x => apply_chartGL hχ h0 hT hK x)

theorem tailCondition_chart (he : IsStrictlyDominant e m) :
    TailCondition (fun l : Fin m => (e ((l : ℕ) + 1) - e l - 1).re) (0 : ℂ).re := by
  rw [Complex.zero_re]
  cases m with
  | zero => intro j; exact j.elim0
  | succ m' =>
    refine tailCondition_of_le (fun l => ?_) ?_
    · have := he l l.isLt
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    · have := he m' (by omega)
      simp only [Complex.sub_re, Complex.one_re, Fin.val_last]
      linarith

end Chart

/-! ## The Jacquet integral of the spherical vector -/

open ComplexPartialJacquet ComplexGramFormula in
/-- **The Jacquet integral of a spherical vector does not vanish.** For strictly dominant
phase-power characters trivial on phases, a `U(n)`-finite principal-series function that is
constant and nonzero on `U(n)` has nonzero Jacquet integral. -/
theorem jacquet_ne_zero : ∀ (n : ℕ) {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}, IsPhasePower χ e →
    IsStrictlyDominant e (n - 1) → (∀ (l : ℕ) (z : ℂˣ), χ l (phaseUnit z) = 1) →
    ∀ {T : Langlands.GeneralLinear n ℂ → ℂ},
    T ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) →
    (∀ k ∈ unitaryCompact ℂ n, T k = T 1) → T 1 ≠ 0 → ComplexJacquetDual.jacquet n T ≠ 0
  | 0, _, _, _, _, _, _, _, _, h1 => h1
  | m + 1, χ, e, hχ, he, h0, T, hT, hK, h1 => by
      have he' : IsStrictlyDominant e m := by simpa using he
      change ComplexJacquetDual.jacquet m (jacquetStep T) ≠ 0
      refine jacquet_ne_zero m hχ.shift (ComplexJacquetDual.isStrictlyDominant_shift he')
        (fun l z => by simp [shiftChar, norm_phaseUnit, h0]) (jacquetStep_mem hχ he' hT)
        (fun k hk => jacquetStep_unitary hT.1 hK hk) ?_
      rw [jacquetStep_one hχ h0 hT.1 hK]
      exact mul_ne_zero h1 (integral_chartFun_ne_zero m _ _ (tailCondition_chart he'))

/-! ## Weight-zero lists -/

open ComplexStrictLanglandsQuotient Langlands.LocalFactor.Archimedean in
theorem complexPositionWeight_eq_zero : ∀ (ds : List ComplexCharacterData),
    (∀ d ∈ ds, d.weight = 0) → ∀ l, complexPositionWeight ds l = 0
  | [], _, _ => rfl
  | d :: _, h, 0 => h d (List.mem_cons_self ..)
  | _ :: ds, h, l + 1 =>
      complexPositionWeight_eq_zero ds (fun d hd => h d (List.mem_cons_of_mem _ hd)) l

end ComplexSphericalJacquet

open ComplexStrictLanglandsQuotient ComplexSphericalJacquet ComplexGramFormula
  Langlands.LocalFactor.Archimedean

/-- **Statement (cyclicity of the spherical vector, strictly ordered case).** Let `ds` be a list
of `n` complex characters `z ↦ |z|^{2 t_i}` (all weights `0`) whose exponents have strictly
decreasing real parts, `Re t_0 > Re t_1 > ⋯`, and let `f₀` be a `U(n)`-finite function of the
standard module of `ds` equal to `1` on `U(n)` (the spherical vector). Then every
`(𝔤𝔩_n(ℂ), U(n))`-submodule of the `U(n)`-finite functions containing `f₀` is everything. -/
def ComplexSphericalCyclicStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData), ds.length = n →
    (∀ d ∈ ds, d.weight = 0) →
    ds.Pairwise (fun d e => e.exponent.re < d.exponent.re) →
    ∀ f₀ : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
    (∀ κ : Matrix.unitaryGroup (Fin n) ℂ,
      (f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ) = 1) →
    ∀ W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
      (∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ w ∈ W, complexStandardRep n ds k w ∈ W) →
      (∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, complexStandardLie n ds Z w ∈ W) →
      f₀ ∈ W → W = ⊤

theorem complexSphericalCyclic : ComplexSphericalCyclicStatement := by
  intro n ds hn
  subst hn
  intro hw hord f₀ hf₀ W hWK hWD hf₀W
  have hχ := isPhasePower ds
  have he := isStrictlyDominant hord
  have h0 : ∀ (l : ℕ) (z : ℂˣ), complexPositionCharacter ds l (phaseUnit z) = 1 := fun l z => by
    rw [complexPositionCharacter_phase, complexPositionWeight_eq_zero ds hw l, zpow_zero]
  by_contra hW'
  obtain ⟨⟨g, hgS⟩, hgW⟩ : ∃ g : (kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length)), g ∉ W := by
    by_contra hcon
    exact hW' (eq_top_iff.mpr fun g _ => by_contra fun h => hcon ⟨g, h⟩)
  have hWX : W.map (kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length)).subtype ≤ kFiniteFunctions (principalSeries ℂ ds.length
      (complexPositionCharacter ds)) (unitaryCompact ℂ ds.length) := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hWK' : ∀ k ∈ unitaryCompact ℂ ds.length, ∀ w ∈ W.map (kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length)).subtype,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear ds.length ℂ) k w ∈
        W.map (kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length)).subtype := by
    intro k hk _ hw
    obtain ⟨w, hwW, rfl⟩ := hw
    refine ⟨complexStandardRep ds.length ds ⟨(k : Matrix (Fin ds.length) (Fin ds.length) ℂ), hk⟩ w,
      hWK _ w hwW, ?_⟩
    change ((complexStandardRep ds.length ds _ w : (kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length))) :
      Langlands.GeneralLinear ds.length ℂ → ℂ) = _
    rw [principalSeriesRep_apply_coe]
    have hku : Unitary.toUnits (⟨(k : Matrix (Fin ds.length) (Fin ds.length) ℂ), hk⟩ :
        Matrix.unitaryGroup (Fin ds.length) ℂ) = k := Units.ext rfl
    rw [hku]
    rfl
  have hWD' : ∀ (X : Matrix (Fin ds.length) (Fin ds.length) ℂ), ∀ w ∈ W.map (kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length)).subtype,
      rightDerivative (matrixModel ℂ ds.length) X w ∈ W.map (kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length)).subtype := by
    intro X _ hw
    obtain ⟨w, hwW, rfl⟩ := hw
    exact ⟨complexStandardLie ds.length ds (1 ⊗ₜ X) w, hWD _ w hwW,
      principalSeriesLie_one_tmul_apply_coe ℂ ds.length (complexPositionCharacter ds) X w⟩
  have hgW' : g ∉ W.map (kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length)).subtype := by
    rintro ⟨w, hwW, hw⟩
    apply hgW
    have : w = ⟨g, hgS⟩ := Subtype.ext hw
    rw [← this]
    exact hwW
  have hker := ComplexJacquetKernel.jacquet_eq_zero_of_proper hχ he _ hWX hWK' hWD' hgS hgW'
  have hj : ComplexJacquetDual.jacquet ds.length
      (f₀ : Langlands.GeneralLinear ds.length ℂ → ℂ) = 0 :=
    (hker ⟨f₀, hf₀W, rfl⟩).2
  have hK1 : ∀ k ∈ unitaryCompact ℂ ds.length,
      (f₀ : Langlands.GeneralLinear ds.length ℂ → ℂ) k = 1 := fun k hk => by
    have hku : Unitary.toUnits (⟨(k : Matrix (Fin ds.length) (Fin ds.length) ℂ), hk⟩ :
        Matrix.unitaryGroup (Fin ds.length) ℂ) = k := Units.ext rfl
    rw [← hku]
    exact hf₀ _
  have h1 : (f₀ : Langlands.GeneralLinear ds.length ℂ → ℂ) 1 = 1 :=
    hK1 1 (unitaryCompact ℂ ds.length).one_mem
  exact jacquet_ne_zero ds.length hχ he h0 f₀.2 (fun k hk => by rw [hK1 k hk, h1])
    (by rw [h1]; exact one_ne_zero) hj

end Langlands.Archimedean
