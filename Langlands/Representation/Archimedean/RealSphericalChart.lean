import Langlands.Representation.Archimedean.RealSphericalReach
import Langlands.Representation.Archimedean.ChartIwasawaPower

/-!
# The spherical and regularized vectors along the chart `J(x, 1)`

For signed-power characters `χ` with exponents `e` and trivial signs on `GL_{m+1}(ℝ)`, the
spherical vector `T₀` (equal to `1` on `O(m+1)`) and the regularized vector `H = q T₀` are
explicit along the chart `x ↦ J(x, 1) ι(k)`, `k ∈ O(m)`:
`T₀(J(x,1) ι(k)) = ∏_{l<m} r_{l+1}(x)^{d_l}` and `H(J(x,1) ι(k)) = r_m(x)^{-1} ∏_{l<m} r_{l+1}(x)^{d_l}`,
with `r_l(x) = 1 + ∑_{j<l} x_j²` and `d_l = (e_{l+1} - e_l - 1)/2`. When the real parts of
`e_0, …, e_m` weakly decrease, the chart function of `H` is integrable with nonzero integral.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealSphericalChart

open ChartIwasawaPower PartialSqIntegral MaximalParabolicIntegration ParabolicChartBound
  PartialJacquet JacquetNonvanishing GramFormula Langlands.GeneralLinear

variable {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} {m : ℕ}

/-- Weakly decreasing real parts of `e_0, …, e_m`. -/
def IsWeaklyDominant (e : ℕ → ℂ) (m : ℕ) : Prop :=
  ∀ l : ℕ, l < m → (e (l + 1)).re ≤ (e l).re

/-- The exponents `d_l = (e_{l+1} - e_l - 1)/2` of the spherical vector along the chart. -/
def chartDiff (e : ℕ → ℂ) (l : Fin m) : ℂ := (e ((l : ℕ) + 1) - e l - 1) / 2

theorem chartDiff_re (l : Fin m) : (chartDiff e l).re = chartExponent e l := by
  simp only [chartDiff, chartExponent, Complex.div_ofNat_re, Complex.sub_re, Complex.one_re]

theorem sign_zero (hp : ∀ l, χ l (-1) = 1) : ∀ l, χ l (-1) = (-1) ^ (fun _ => 0 : ℕ → ℕ) l :=
  fun l => by rw [hp l, pow_zero]

/-- **The spherical vector along the chart.** -/
theorem spherical_chart (hχ : IsSignedPower χ e) (hp : ∀ l, χ l (-1) = 1) (x : Fin m → ℝ)
    {κ : Langlands.GeneralLinear (m + 1) ℝ} (hκ : κ ∈ unitaryCompact ℝ (m + 1)) :
    signVector (m + 1) e (fun _ => 0) (fun _ => 0) (chartGL x * κ) =
      ∏ l : Fin m, ((partialSq x ((l : ℕ) + 1) : ℝ) : ℂ) ^ chartDiff e l := by
  obtain ⟨a, u, k, hk, hg⟩ :=
    exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact (chartGL x)
  have hmem := (signVector_mem (n := m + 1) (fun _ => 0) (fun _ => 0) hχ (sign_zero hp)).1
  have hsign : ∀ l : Fin (m + 1), χ l (-1) =
      if l ∈ (∅ : Finset (Fin (m + 1))) then -1 else 1 := fun l => by
    simp [hp]
  have hkκ : k * κ ∈ unitaryCompact ℝ (m + 1) := mul_mem hk hκ
  have h1 := principalSeriesCharacter_mul_prod_zpow hχ hsign (σ := 1) (Or.inl rfl) a
  rw [Finset.prod_empty, Complex.ofReal_one, _root_.one_zpow, mul_one] at h1
  rw [hg, mul_assoc, hmem.2 a u (k * κ), signVector_of_mem _ _ hkκ, h1,
    prod_abs_cpow_chart x a u k hk hg]
  have hone : signMonomial (m + 1) (fun _ => 0) (fun _ => 0)
      ⟨((k * κ : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ),
        hkκ⟩ = 1 := by
    simp [signMonomial]
  rw [hone, mul_one]
  refine Finset.prod_congr rfl fun l _ => ?_
  congr 1
  simp only [torusExponent, chartDiff, Fin.val_succ, Fin.val_castSucc, Finset.notMem_empty,
    ite_false, add_zero]
  push_cast
  ring

theorem partialSq_last (x : Fin m → ℝ) :
    partialSq x m = 1 + OrthogonalLastRowIntegral.sqNorm x := by
  simp [partialSq, OrthogonalLastRowIntegral.sqNorm]

/-- **The regularized vector along the chart.** -/
theorem regularized_chart (hχ : IsSignedPower χ e) (hp : ∀ l, χ l (-1) = 1) (x : Fin m → ℝ)
    {k : Langlands.GeneralLinear m ℝ} (hk : k ∈ unitaryCompact ℝ m) :
    signVector (m + 1) e (fun _ => 0) (bump (fun _ => 0) m 1) (chartGL x * iotaGL k) =
      partialSqProd (chartDiff e) (-1) x := by
  rw [signVector_bump (fun _ => 0) (fun _ => 0) hχ (sign_zero hp) 1, qFun_chart x hk,
    spherical_chart hχ hp x (iotaGL_mem_unitaryCompact hk), partialSqProd, pow_one,
    Complex.cpow_neg_one, partialSq_last, Complex.ofReal_inv]

theorem norm_partialSqProd_chartDiff (x : Fin m → ℝ) :
    ‖partialSqProd (chartDiff e) (-1) x‖ =
      partialSq x m ^ (-1 : ℝ) * ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ chartExponent e l := by
  rw [norm_partialSqProd]
  simp only [chartDiff_re, Complex.neg_re, Complex.one_re]

/-- **The tail condition.** For weakly decreasing real parts, `d` satisfies the tail condition
with `c = -1`. -/
theorem tailCondition_chartDiff (he : IsWeaklyDominant e m) :
    TailCondition (chartDiff (m := m) e) (-1) := by
  intro j
  have hle : ∑ l : Fin m, (if j ≤ l then (chartDiff e l).re + 1 / 2 else 0) ≤ 0 := by
    refine Finset.sum_nonpos fun l _ => ?_
    split_ifs
    · have := he l l.isLt
      rw [chartDiff_re]
      unfold chartExponent
      linarith
    · exact le_rfl
  simp only [Complex.neg_re, Complex.one_re]
  linarith

/-- **The chart integral of the regularized vector does not vanish.** -/
theorem integral_regularized_ne_zero (he : IsWeaklyDominant e m) :
    Integrable (partialSqProd (chartDiff (m := m) e) (-1)) ∧
      ∫ x, partialSqProd (chartDiff (m := m) e) (-1) x ≠ 0 :=
  integrable_and_integral_ne_zero m _ _ (tailCondition_chartDiff he)

/-- The partial Jacquet integral of the regularized vector is constant on `O(m)`. -/
theorem jacquetStep_regularized (hχ : IsSignedPower χ e) (hp : ∀ l, χ l (-1) = 1)
    {k : Langlands.GeneralLinear m ℝ} (hk : k ∈ unitaryCompact ℝ m) :
    jacquetStep (signVector (m + 1) e (fun _ => 0) (bump (fun _ => 0) m 1)) k =
      ∫ x, partialSqProd (chartDiff (m := m) e) (-1) x := by
  unfold jacquetStep
  simp_rw [regularized_chart hχ hp _ hk]

end RealSphericalChart

end Langlands.Archimedean
