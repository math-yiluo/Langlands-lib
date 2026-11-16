import Langlands.Representation.Archimedean.PartialSqIntegral
import Langlands.Representation.Archimedean.PartialJacquetIntegral

/-!
# Powers of the Iwasawa torus coordinates along the chart `J(x, 1)`
-/

noncomputable section

open MeasureTheory

namespace Langlands.Archimedean

set_option autoImplicit false

namespace ChartIwasawaPower

open ParabolicChartBound PartialSqIntegral PartialJacquet MaximalParabolicIntegration
  GramFormula Langlands.GeneralLinear

/-! ## Tail products -/

/-- `ρ_l = ∏_{j ≥ l} α_j`. -/
def tailProd {N : ℕ} (α : Fin N → ℝ) (l : ℕ) : ℝ :=
  ∏ j : Fin N, if l ≤ (j : ℕ) then α j else 1

theorem tailProd_succ {N : ℕ} (α : Fin (N + 1) → ℝ) (l : ℕ) :
    tailProd α (l + 1) = tailProd (fun j => α j.succ) l := by
  unfold tailProd
  rw [Fin.prod_univ_succ]
  simp [Fin.val_succ]

theorem tailProd_zero {N : ℕ} (α : Fin (N + 1) → ℝ) : tailProd α 0 = α 0 * tailProd α 1 := by
  rw [tailProd_succ]
  unfold tailProd
  rw [Fin.prod_univ_succ]
  simp

theorem tailProd_pos {N : ℕ} {α : Fin N → ℝ} (hα : ∀ j, 0 < α j) (l : ℕ) : 0 < tailProd α l :=
  Finset.prod_pos fun j _ => by split_ifs; exacts [hα j, one_pos]

/-- **Abel summation for complex powers.** For positive `α_0, …, α_m` with tail products
`ρ_l = ∏_{j ≥ l} α_j`: `∏_l α_l^{t_l} = ρ_0^{t_0} ∏_{l<m} ρ_{l+1}^{t_{l+1} - t_l}`. -/
theorem prod_cpow_eq_tailProd : ∀ (m : ℕ) (α : Fin (m + 1) → ℝ), (∀ j, 0 < α j) →
    ∀ t : Fin (m + 1) → ℂ,
    ∏ l, ((α l : ℝ) : ℂ) ^ t l = ((tailProd α 0 : ℝ) : ℂ) ^ t 0 *
      ∏ l : Fin m, ((tailProd α ((l : ℕ) + 1) : ℝ) : ℂ) ^ (t l.succ - t (Fin.castSucc l))
  | 0, α, hα, t => by
      have h0 : tailProd α 0 = α 0 := by simp [tailProd]
      simp [h0]
  | m + 1, α, hα, t => by
      have ih := prod_cpow_eq_tailProd m (fun j => α j.succ) (fun j => hα _) (fun j => t j.succ)
      rw [Fin.prod_univ_succ, ih, Fin.prod_univ_succ]
      simp only [← tailProd_succ, Fin.val_zero, zero_add, Fin.val_succ, Fin.succ_zero_eq_one,
        Fin.castSucc_zero, Fin.succ_castSucc]
      have hρ1 : 0 < tailProd α 1 := tailProd_pos hα 1
      have hα0 : 0 < α 0 := hα 0
      rw [tailProd_zero, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hα0.le hρ1.le]
      have hne : ((tailProd α 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ1.ne'
      have hsplit : ((tailProd α 1 : ℝ) : ℂ) ^ t 1 =
          ((tailProd α 1 : ℝ) : ℂ) ^ t 0 * ((tailProd α 1 : ℝ) : ℂ) ^ (t 1 - t 0) := by
        rw [← Complex.cpow_add _ _ hne]
        ring_nf
      rw [hsplit]
      ring

/-! ## The chart `J(x, 1)` -/

variable {m : ℕ}

theorem tailProd_abs_chart (x : Fin m → ℝ) (a : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ)
    (k : Langlands.GeneralLinear (m + 1) ℝ) (hk : k ∈ unitaryCompact ℝ (m + 1))
    (hg : chartGL x = (Iwasawa.diagonalUnits a : Langlands.GeneralLinear (m + 1) ℝ) *
      (u : Langlands.GeneralLinear (m + 1) ℝ) * k) {l : ℕ} (hl : l ≤ m) :
    tailProd (fun j => |(a j : ℝ)|) l = Real.sqrt (partialSq x l) := by
  have h := prod_tail_sq_eq x 1 (one_mem _) a u k hk (by rw [mul_one]; exact hg) hl
  rw [← h, Real.sqrt_sq_eq_abs, Finset.abs_prod]
  unfold tailProd
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- **Torus powers along the chart.** If `J(x,1) = diag(a) u k`, then
`∏_l |a_l|^{t_l} = ∏_{l<m} r_{l+1}(x)^{(t_{l+1} - t_l)/2}`. -/
theorem prod_abs_cpow_chart (x : Fin m → ℝ) (a : Fin (m + 1) → ℝˣ)
    (u : upperUnipotent (m + 1) ℝ) (k : Langlands.GeneralLinear (m + 1) ℝ)
    (hk : k ∈ unitaryCompact ℝ (m + 1))
    (hg : chartGL x = (Iwasawa.diagonalUnits a : Langlands.GeneralLinear (m + 1) ℝ) *
      (u : Langlands.GeneralLinear (m + 1) ℝ) * k) (t : Fin (m + 1) → ℂ) :
    ∏ l, ((|(a l : ℝ)| : ℝ) : ℂ) ^ t l =
      ∏ l : Fin m, ((partialSq x ((l : ℕ) + 1) : ℝ) : ℂ) ^ ((t l.succ - t (Fin.castSucc l)) / 2) := by
  rw [prod_cpow_eq_tailProd m (fun j => |(a j : ℝ)|) (fun j => abs_pos.mpr (a j).ne_zero) t,
    tailProd_abs_chart x a u k hk hg (Nat.zero_le _), partialSq_zero, Real.sqrt_one,
    Complex.ofReal_one, Complex.one_cpow, one_mul]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [tailProd_abs_chart x a u k hk hg (by omega), Real.sqrt_eq_rpow,
    ← Complex.cpow_mul_ofReal_nonneg (partialSq_pos x _).le]
  congr 1
  push_cast
  ring

/-! ## Signed characters times signed monomials -/

theorem signUnit_of_pos {y : ℝˣ} (hy : 0 < (y : ℝ)) : signUnit y = 1 := by
  simp [signUnit, hy]

theorem signUnit_of_neg {y : ℝˣ} (hy : (y : ℝ) < 0) : signUnit y = -1 := by
  simp [signUnit, not_lt.mpr hy.le]

/-- An odd sign character times the matching power of `y`. -/
theorem char_mul_zpow_odd {χl : ℝˣ → ℂ} {el : ℂ}
    (heq : ∀ y : ℝˣ, χl y = χl (signUnit y) * ((|(y : ℝ)| : ℝ) : ℂ) ^ el) (hone : χl 1 = 1)
    (hneg : χl (-1) = -1) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (y : ℝˣ) :
    χl y * (((y : ℝ) : ℂ) ^ σ) = ((|(y : ℝ)| : ℝ) : ℂ) ^ (el + σ) := by
  have habs : ((|(y : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr y.ne_zero)
  rw [heq y, Complex.cpow_add _ _ habs, Complex.cpow_intCast]
  rcases lt_or_gt_of_ne y.ne_zero with hy | hy
  · rw [signUnit_of_neg hy, hneg, abs_of_neg hy]
    rcases hσ with rfl | rfl
    · simp only [zpow_one, Complex.ofReal_neg]
      ring
    · simp only [Complex.ofReal_neg, zpow_neg, zpow_one, inv_neg]
      ring
  · rw [signUnit_of_pos hy, hone, abs_of_pos hy]
    ring

/-- An even sign character. -/
theorem char_eq_abs_cpow_even {χl : ℝˣ → ℂ} {el : ℂ}
    (heq : ∀ y : ℝˣ, χl y = χl (signUnit y) * ((|(y : ℝ)| : ℝ) : ℂ) ^ el) (hone : χl 1 = 1)
    (hneg : χl (-1) = 1) (y : ℝˣ) :
    χl y = ((|(y : ℝ)| : ℝ) : ℂ) ^ el := by
  rw [heq y]
  rcases lt_or_gt_of_ne y.ne_zero with hy | hy
  · rw [signUnit_of_neg hy, hneg, one_mul]
  · rw [signUnit_of_pos hy, hone, one_mul]

/-- The exponents `t_l = e_l + (N-1)/2 - l + σ [l ∈ I]`. -/
def torusExponent {N : ℕ} (e : ℕ → ℂ) (I : Finset (Fin N)) (σ : ℤ) (l : Fin N) : ℂ :=
  e l + ((N : ℂ) - 1) / 2 - ((l : ℕ) : ℂ) + if l ∈ I then (σ : ℂ) else 0

/-- **The principal-series character times a signed monomial.** If `χ_l(-1) = -1` exactly
for `l ∈ I`, then `χδ^{1/2}(a) (∏_{i∈I} a_i)^σ = ∏_l |a_l|^{t_l}` for `σ = ±1`. -/
theorem principalSeriesCharacter_mul_prod_zpow {N : ℕ} {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}
    (hχ : IsSignedPower χ e) {I : Finset (Fin N)}
    (hsign : ∀ l : Fin N, χ l (-1) = if l ∈ I then -1 else 1) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (a : Fin N → ℝˣ) :
    principalSeriesCharacter ℝ N χ a * (((∏ i ∈ I, (a i : ℝ) : ℝ) : ℂ) ^ σ) =
      ∏ l, ((|(a l : ℝ)| : ℝ) : ℂ) ^ torusExponent e I σ l := by
  have hI : (((∏ i ∈ I, (a i : ℝ) : ℝ) : ℂ) ^ σ) =
      ∏ l, (if l ∈ I then (((a l : ℝ) : ℂ) ^ σ) else 1) := by
    rw [Complex.ofReal_prod, ← Finset.prod_zpow, ← Finset.prod_filter, Finset.filter_mem_eq_inter,
      Finset.univ_inter]
  rw [hI, principalSeriesCharacter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  have habs : ((|(a l : ℝ)| : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (a l).ne_zero)
  simp only [Module.finrank_self, pow_one, Real.norm_eq_abs]
  unfold torusExponent
  split_ifs with hl
  · rw [mul_right_comm, char_mul_zpow_odd (hχ.eq l) (hχ.one l) (by simp [hsign l, hl]) hσ
      (a l), ← Complex.cpow_add _ _ habs]
    congr 1
    ring
  · rw [mul_one, char_eq_abs_cpow_even (hχ.eq l) (hχ.one l) (by simp [hsign l, hl]) (a l),
      ← Complex.cpow_add _ _ habs]
    congr 1
    ring

/-! ## The tail condition along the chart -/

theorem re_lt_of_lt {e : ℕ → ℂ} {m : ℕ} (he : IsStrictlyDominant e m) :
    ∀ {j k : ℕ}, j < k → k ≤ m → (e k).re < (e j).re
  | _, 0, hjk, _ => absurd hjk (Nat.not_lt_zero _)
  | j, k + 1, hjk, hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with h | h
      · have h1 := re_lt_of_lt he h (by omega)
        have h2 := he k (by omega)
        linarith
      · subst h
        exact he j (by omega)

/-- **The tail condition for the exponents of the chart.** If the real parts of `e` strictly
decrease on `0, …, m` and `σ = -1` for `m ∈ I`, `σ = 1` for `m ∉ I`, then the exponents
`d_l = (t_{l+1} - t_l)/2` with `t = torusExponent e I σ` satisfy the tail condition. -/
theorem tailCondition_torusExponent {m : ℕ} {e : ℕ → ℂ} (he : IsStrictlyDominant e m)
    {I : Finset (Fin (m + 1))} {σ : ℤ} (hσ : σ = if Fin.last m ∈ I then -1 else 1) :
    TailCondition (fun l : Fin m =>
      (torusExponent e I σ l.succ - torusExponent e I σ (Fin.castSucc l)) / 2) 0 := by
  rcases m with _ | m
  · intro j
    exact j.elim0
  intro j
  set F : Fin (m + 2) → ℝ := fun l => (torusExponent e I σ l).re / 2 + ((l : ℕ) : ℝ) / 2 with hF
  have hsummand : ∀ l : Fin (m + 1),
      ((torusExponent e I σ l.succ - torusExponent e I σ (Fin.castSucc l)) / 2).re + 1 / 2 =
        F l.succ - F (Fin.castSucc l) := by
    intro l
    simp only [hF, Fin.val_succ, Fin.val_castSucc, Complex.div_ofNat_re, Complex.sub_re]
    push_cast
    ring
  simp only [Complex.zero_re, zero_add, hsummand]
  have hfilter : (∑ l : Fin (m + 1), if j ≤ l then F l.succ - F (Fin.castSucc l) else 0) =
      ∑ l ∈ Finset.Icc j (Fin.last m), (F l.succ - F (Fin.castSucc l)) := by
    rw [← Finset.sum_filter]
    congr 1
    ext l
    simp [Fin.le_last]
  rw [hfilter, Fin.sum_Icc_sub (Fin.le_last j), Fin.succ_last]
  have hlt : (e (m + 1)).re < (e j).re := re_lt_of_lt he j.isLt le_rfl
  simp only [hF, torusExponent, Fin.val_last, Fin.val_castSucc]
  by_cases hl : Fin.last (m + 1) ∈ I <;> by_cases hj : Fin.castSucc j ∈ I <;>
    simp [hl, hj, hσ] <;> linarith

end ChartIwasawaPower

end Langlands.Archimedean
