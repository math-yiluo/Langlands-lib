import Langlands.Representation.Archimedean.JacquetKernel

/-!
# The Jacquet integral does not vanish on strictly dominant principal series
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace JacquetNonvanishing

open MaximalParabolicIntegration ParabolicChartBound PartialJacquet JacquetLimit JacquetDual
  JacquetKernel GramFormula Langlands.GeneralLinear RealPrincipalSeriesDuality
  PrincipalSeriesExtension TranslateFinite

variable {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

/-! ## Continuity of the Jacquet integral -/

/-- **Continuity.** The Jacquet integral is continuous for convergence on `O(n)` that is
bounded uniformly on `O(n)`. -/
theorem tendsto_jacquet : ∀ (n : ℕ) {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}, IsSignedPower χ e →
    IsStrictlyDominant e (n - 1) →
    ∀ {f : ℕ → Langlands.GeneralLinear n ℝ → ℂ} {f₀ : Langlands.GeneralLinear n ℝ → ℂ},
    (∀ N, f N ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)) →
    f₀ ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) →
    ∀ {C : ℝ}, (∀ N, ∀ k ∈ unitaryCompact ℝ n, ‖f N k‖ ≤ C) →
    (∀ k ∈ unitaryCompact ℝ n, Tendsto (fun N => f N k) atTop (𝓝 (f₀ k))) →
    Tendsto (fun N => jacquet n (f N)) atTop (𝓝 (jacquet n f₀))
  | 0, _, _, _, _, _, _, _, _, _, _, hlim => hlim 1 (unitaryCompact ℝ 0).one_mem
  | m + 1, χ, e, hχ, he, f, f₀, hf, hf₀, C, hC, hlim => by
      have he' : IsStrictlyDominant e m := by simpa using he
      set D : (Fin m → ℝ) → ℝ := fun x => C * ∏ l : Fin m, (1 + x l ^ 2) ^ chartExponent e l
        with hD
      have hDi : Integrable D :=
        (integrable_prod_one_add_sq_rpow (chartExponent_lt he')).const_mul C
      refine tendsto_jacquet m hχ.shift (isStrictlyDominant_shift he')
        (fun N => jacquetStep_mem hχ he' (hf N)) (jacquetStep_mem hχ he' hf₀) (C := ∫ x, D x)
        (fun N k hk => ?_) (fun k hk => ?_)
      · exact norm_integral_le_of_norm_le hDi (ae_of_all _ fun x =>
          norm_le_of_mem_principalSeries hχ he' (hf N).1 (hC N) x (iotaGL_mem_unitaryCompact hk))
      · refine tendsto_integral_of_dominated_convergence D (fun N =>
          ((hf N).1.1.continuous.comp (continuous_chartGL.mul continuous_const)).aestronglyMeasurable)
          hDi (fun N => ae_of_all _ fun x => norm_le_of_mem_principalSeries hχ he' (hf N).1 (hC N)
            x (iotaGL_mem_unitaryCompact hk)) (ae_of_all _ fun x => ?_)
        obtain ⟨a, u, κ, hκ, hy⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact
          (chartGL x * iotaGL k)
        have h1 : (fun N => f N (chartGL x * iotaGL k)) =
            fun N => principalSeriesCharacter ℝ (m + 1) χ a * f N κ :=
          funext fun N => by rw [hy, (hf N).1.2 a u κ]
        rw [h1, hy, hf₀.1.2 a u κ]
        exact (hlim κ hκ).const_mul _

/-! ## Sign monomials -/

/-- The sign monomial `κ ↦ ∏_l κ_ll^{p_l + 2 a_l}` on `O(n)`. -/
def signMonomial (n : ℕ) (p a : ℕ → ℕ) (κ : Matrix.unitaryGroup (Fin n) ℝ) : ℂ :=
  ∏ l : Fin n, ((((κ : Matrix (Fin n) (Fin n) ℝ) l l : ℝ) : ℂ)) ^ (p l + 2 * a l)

variable {n : ℕ} (p a : ℕ → ℕ)

theorem continuous_signMonomial : Continuous (signMonomial n p a) :=
  continuous_finsetProd _ fun l _ => (Complex.continuous_ofReal.comp
    ((continuous_apply l).comp ((continuous_apply l).comp continuous_subtype_val))).pow _

theorem finiteDimensional_signMonomial :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ =>
      fun x => signMonomial n p a (x * k))) := by
  have h := finiteDimensional_span_eval (n := n)
    (∏ l : Fin n, MvPolynomial.X (l, l) ^ (p l + 2 * a l))
  have heq : (fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => signMonomial n p a (x * k)) =
      fun k x => MvPolynomial.eval (fun ij => (((x * k : Matrix.unitaryGroup (Fin n) ℝ) :
        Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℂ))
          (∏ l : Fin n, MvPolynomial.X (l, l) ^ (p l + 2 * a l)) :=
    funext fun k => funext fun x => by simp [signMonomial, map_prod]
  rw [heq]
  exact h

theorem signReal_pow_eq (hp : ∀ l, χ l (-1) = (-1) ^ p l) (hχ1 : ∀ l, χ l 1 = 1) (l : ℕ)
    (d : ℝˣ) : ((signReal (d : ℝ) : ℝ) : ℂ) ^ (p l + 2 * a l) = χ l (signUnit d) := by
  unfold signReal signUnit
  split_ifs
  · simp [hχ1]
  · rw [hp, pow_add, pow_mul]
    push_cast
    simp

theorem signMonomial_signDiagonal (hp : ∀ l, χ l (-1) = (-1) ^ p l) (hχ1 : ∀ l, χ l 1 = 1)
    (d : Fin n → ℝˣ) (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    signMonomial n p a (signDiagonal (fun i => (d i : ℝ)) * κ) =
      principalSeriesCharacter ℝ n χ (fun i => signUnit (d i)) * signMonomial n p a κ := by
  rw [principalSeriesCharacter_sign, signMonomial, signMonomial, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  change ((((Matrix.diagonal fun i => signReal (d i : ℝ)) * (κ : Matrix (Fin n) (Fin n) ℝ)) l l :
    ℝ) : ℂ) ^ (p l + 2 * a l) = _
  rw [Matrix.diagonal_mul, Complex.ofReal_mul, mul_pow, signReal_pow_eq p a hp hχ1]

/-- The function of the principal series extending the sign monomial. -/
def signVector (n : ℕ) (e : ℕ → ℂ) (p a : ℕ → ℕ) : Langlands.GeneralLinear n ℝ → ℂ :=
  extension (shiftedExponent n e) (signMonomial n p a)

theorem signVector_mem (hχ : IsSignedPower χ e) (hp : ∀ l, χ l (-1) = (-1) ^ p l) :
    signVector n e p a ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) :=
  extension_mem_kFiniteFunctions e hχ.eq (continuous_signMonomial p a)
    (finiteDimensional_signMonomial p a) (signMonomial_signDiagonal p a hp hχ.one)

theorem signVector_unitary (κ : Matrix.unitaryGroup (Fin n) ℝ) :
    signVector n e p a (Unitary.toUnits κ) = signMonomial n p a κ :=
  extension_unitary _ _ _

theorem signVector_of_mem {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    signVector n e p a k = signMonomial n p a ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ := by
  have hku : k = Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ :
      Matrix.unitaryGroup (Fin n) ℝ) := Units.ext rfl
  calc signVector n e p a k = signVector n e p a (Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℝ),
        hk⟩ : Matrix.unitaryGroup (Fin n) ℝ)) := congrArg _ hku
    _ = _ := signVector_unitary p a _

theorem signVector_iota {m : ℕ} (e' : ℕ → ℂ) {k : Langlands.GeneralLinear m ℝ}
    (hk : k ∈ unitaryCompact ℝ m) :
    signVector (m + 1) e p a (iotaGL k) = signVector m e' p a k := by
  rw [signVector_of_mem p a (iotaGL_mem_unitaryCompact hk), signVector_of_mem p a hk,
    signMonomial, signMonomial, Fin.prod_univ_castSucc]
  simp only [iotaGL_val, iota_castSucc_castSucc, iota_last_last, Fin.val_castSucc,
    Complex.ofReal_one, one_pow, mul_one]

/-! ## The concentrating function `q(y) = y_{mm}² / |y_m|²` -/

/-- `q(y) = y_{mm}² / ∑_j y_{mj}²`, a function of the last row. -/
def qFun {m : ℕ} (y : Langlands.GeneralLinear (m + 1) ℝ) : ℝ :=
  ((y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (Fin.last m) (Fin.last m)) ^ 2 /
    ∑ j, ((y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (Fin.last m) j) ^ 2

theorem lastRow_diagonalUnits_mul {m : ℕ} (b : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ)
    (y : Langlands.GeneralLinear (m + 1) ℝ) (j : Fin (m + 1)) :
    (((Iwasawa.diagonalUnits b : Langlands.GeneralLinear (m + 1) ℝ) *
      (u : Langlands.GeneralLinear (m + 1) ℝ) * y : Langlands.GeneralLinear (m + 1) ℝ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (Fin.last m) j =
      (b (Fin.last m) : ℝ) * (y : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (Fin.last m) j := by
  rw [Units.val_mul, Units.val_mul, Iwasawa.diagonalUnits_val, Matrix.mul_assoc,
    Matrix.diagonal_mul, Matrix.mul_apply]
  congr 1
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [u.2.2 (Fin.last m), one_mul]
  · intro l _ hl
    have hlt : l < Fin.last m := lt_of_le_of_ne (Fin.le_last l) hl
    rw [show ((u : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
      (Fin.last m) l = 0 from u.2.1 hlt, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem qFun_mul {m : ℕ} (b : Fin (m + 1) → ℝˣ) (u : upperUnipotent (m + 1) ℝ)
    (y : Langlands.GeneralLinear (m + 1) ℝ) :
    qFun ((Iwasawa.diagonalUnits b : Langlands.GeneralLinear (m + 1) ℝ) *
      (u : Langlands.GeneralLinear (m + 1) ℝ) * y) = qFun y := by
  unfold qFun
  simp only [lastRow_diagonalUnits_mul, mul_pow, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (b (Fin.last m)).ne_zero)

theorem qFun_of_mem {m : ℕ} {κ : Langlands.GeneralLinear (m + 1) ℝ}
    (hκ : κ ∈ unitaryCompact ℝ (m + 1)) :
    qFun κ = ((κ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (Fin.last m) (Fin.last m)) ^ 2 := by
  have h := sqNorm_lastRow (⟨κ, hκ⟩ : unitaryCompact ℝ (m + 1))
  unfold OrthogonalLastRowIntegral.sqNorm OrthogonalLastRowIntegral.lastRow at h
  unfold qFun
  rw [show (∑ j, ((κ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (Fin.last m) j) ^ 2) = 1 from h,
    div_one]

/-- The exponents `a` with `N` added at position `m`. -/
def bump (a : ℕ → ℕ) (m N : ℕ) (l : ℕ) : ℕ := a l + if l = m then N else 0

theorem signVector_bump {m : ℕ} (hχ : IsSignedPower χ e) (hp : ∀ l, χ l (-1) = (-1) ^ p l)
    (N : ℕ) (y : Langlands.GeneralLinear (m + 1) ℝ) :
    signVector (m + 1) e p (bump a m N) y = (qFun y : ℂ) ^ N * signVector (m + 1) e p a y := by
  obtain ⟨b, u, κ, hκ, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact y
  rw [(signVector_mem p (bump a m N) hχ hp).1.2 b u κ, (signVector_mem p a hχ hp).1.2 b u κ,
    qFun_mul, qFun_of_mem hκ, signVector_of_mem _ _ hκ, signVector_of_mem _ _ hκ, signMonomial,
    signMonomial, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  have hcs : ∀ l : Fin m, bump a m N (l : ℕ) = a l := fun l => by
    simp [bump, (Fin.isLt l).ne]
  have hlast : bump a m N m = a m + N := by simp [bump]
  simp only [Fin.val_castSucc, Fin.val_last, hcs, hlast]
  push_cast
  ring

theorem lastRow_chartGL_mul_iotaGL {m : ℕ} (x : Fin m → ℝ) (k : Langlands.GeneralLinear m ℝ)
    (j : Fin (m + 1)) :
    ((chartGL x * iotaGL k : Langlands.GeneralLinear (m + 1) ℝ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (Fin.last m) j =
      Fin.lastCases 1 (fun j' => (x ᵥ* (k : Matrix (Fin m) (Fin m) ℝ)) j') j := by
  rw [Units.val_mul, chartGL, JGL_val, iotaGL_val, Matrix.mul_apply, Jmat_last,
    Fin.sum_univ_castSucc]
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp
  · simp [Matrix.vecMul, dotProduct]

theorem qFun_chart {m : ℕ} (x : Fin m → ℝ) {k : Langlands.GeneralLinear m ℝ}
    (hk : k ∈ unitaryCompact ℝ m) :
    qFun (chartGL x * iotaGL k) = (1 + OrthogonalLastRowIntegral.sqNorm x)⁻¹ := by
  unfold qFun
  simp only [lastRow_chartGL_mul_iotaGL, Fin.sum_univ_castSucc, Fin.lastCases_last,
    Fin.lastCases_castSucc]
  have h := OrthogonalLastRowIntegral.sqNorm_vecMul
    (OrthogonalLastRowIntegral.mul_transpose_eq_one ⟨k, hk⟩) x
  unfold OrthogonalLastRowIntegral.sqNorm at h ⊢
  rw [h]
  ring

/-! ## The approximate identity -/

theorem bernoulli_pow {s : ℝ} (hs : 0 ≤ s) {N₀ N : ℕ} (h0 : 0 < N₀) (hN : N₀ ≤ N) :
    (1 + s / N₀) ^ N₀ ≤ (1 + s / N) ^ N := by
  have hN0 : (0 : ℝ) < N₀ := by exact_mod_cast h0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le h0 hN
  have hp : (1 : ℝ) ≤ (N : ℝ) / N₀ := by
    rw [le_div_iff₀ hN0, one_mul]
    exact_mod_cast hN
  have hs' : (-1 : ℝ) ≤ s / N := by
    have : 0 ≤ s / N := div_nonneg hs hNpos.le
    linarith
  have hb := one_add_mul_self_le_rpow_one_add hs' hp
  have h1 : (N : ℝ) / N₀ * (s / N) = s / N₀ := by field_simp
  rw [h1] at hb
  have hbase : 0 ≤ 1 + s / N := by positivity
  calc (1 + s / N₀) ^ N₀ ≤ ((1 + s / N) ^ ((N : ℝ) / N₀)) ^ N₀ :=
        pow_le_pow_left₀ (by positivity) hb N₀
    _ = (1 + s / N) ^ N := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hbase, div_mul_cancel₀ _ hN0.ne',
          Real.rpow_natCast]

theorem continuous_sqNorm {m : ℕ} :
    Continuous fun y : Fin m → ℝ => OrthogonalLastRowIntegral.sqNorm y := by
  unfold OrthogonalLastRowIntegral.sqNorm
  fun_prop

theorem integrable_inv_one_add_div_pow (m : ℕ) :
    Integrable fun y : Fin m → ℝ =>
      ((1 + OrthogonalLastRowIntegral.sqNorm y / ((m + 1 : ℕ) : ℝ)) ^ (m + 1))⁻¹ := by
  have hN0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hint := integrable_rpow_neg_one_add_norm_sq (E := Fin m → ℝ) (μ := volume)
    (r := 2 * ((m + 1 : ℕ) : ℝ)) (by rw [Module.finrank_fin_fun]; push_cast; linarith)
  have hcont : Continuous fun y : Fin m → ℝ =>
      ((1 + OrthogonalLastRowIntegral.sqNorm y / ((m + 1 : ℕ) : ℝ)) ^ (m + 1))⁻¹ := by
    refine Continuous.inv₀ ((continuous_const.add (continuous_sqNorm.div_const _)).pow _)
      fun y => (pow_pos (by
        have := OrthogonalLastRowIntegral.sqNorm_nonneg y
        positivity) _).ne'
  refine (hint.const_mul (((m + 1 : ℕ) : ℝ) ^ (m + 1))).mono' hcont.aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  have hs := OrthogonalLastRowIntegral.norm_sq_le_sqNorm y
  have hs0 := OrthogonalLastRowIntegral.sqNorm_nonneg y
  have hpos : 0 < 1 + ‖y‖ ^ 2 := by positivity
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg (by positivity) _))]
  have h1 : (1 + ‖y‖ ^ 2) / ((m + 1 : ℕ) : ℝ) ≤
      1 + OrthogonalLastRowIntegral.sqNorm y / ((m + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hN0, add_mul, div_mul_cancel₀ _ hN0.ne', one_mul]
    have : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    linarith
  have h2 : ((1 + ‖y‖ ^ 2) / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) ≤
      (1 + OrthogonalLastRowIntegral.sqNorm y / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) :=
    pow_le_pow_left₀ (by positivity) h1 _
  have h3 : (1 + ‖y‖ ^ 2) ^ (-(2 * ((m + 1 : ℕ) : ℝ)) / 2) = ((1 + ‖y‖ ^ 2) ^ (m + 1))⁻¹ := by
    rw [show -(2 * ((m + 1 : ℕ) : ℝ)) / 2 = -((m + 1 : ℕ) : ℝ) by ring, Real.rpow_neg hpos.le,
      Real.rpow_natCast]
  rw [h3]
  calc ((1 + OrthogonalLastRowIntegral.sqNorm y / ((m + 1 : ℕ) : ℝ)) ^ (m + 1))⁻¹
      ≤ (((1 + ‖y‖ ^ 2) / ((m + 1 : ℕ) : ℝ)) ^ (m + 1))⁻¹ :=
        inv_anti₀ (pow_pos (by positivity) _) h2
    _ = ((m + 1 : ℕ) : ℝ) ^ (m + 1) * ((1 + ‖y‖ ^ 2) ^ (m + 1))⁻¹ := by
        rw [div_pow, inv_div, div_eq_mul_inv]

theorem norm_chart_le_of_mem {m : ℕ} (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e m)
    {H : Langlands.GeneralLinear (m + 1) ℝ → ℂ} (hH : H ∈ principalSeries ℝ (m + 1) χ) {C : ℝ}
    (hC : ∀ k ∈ unitaryCompact ℝ (m + 1), ‖H k‖ ≤ C) (x : Fin m → ℝ)
    {κ : Langlands.GeneralLinear (m + 1) ℝ} (hκ : κ ∈ unitaryCompact ℝ (m + 1)) :
    ‖H (chartGL x * κ)‖ ≤ C := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1 (unitaryCompact ℝ (m + 1)).one_mem)
  refine (norm_le_of_mem_principalSeries hχ he hH hC x hκ).trans ?_
  refine mul_le_of_le_one_right hC0 (Finset.prod_le_one₀ (fun l _ =>
    (Real.rpow_pos_of_pos (by positivity) _).le) fun l _ =>
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg (x l)]) ?_)
  have := chartExponent_lt he l
  linarith

theorem integral_scale {m : ℕ} (f : (Fin m → ℝ) → ℂ) {c : ℝ} (hc : 0 < c) :
    ((c ^ m : ℝ) : ℂ) * ∫ x, f x = ∫ y, f (c⁻¹ • y) := by
  rw [Measure.integral_comp_smul, Module.finrank_fin_fun, Complex.real_smul,
    show |(c⁻¹ ^ m)⁻¹| = c ^ m by rw [abs_inv, abs_pow, abs_inv, abs_of_pos hc, inv_pow, inv_inv]]

/-- **Approximate identity.** With `N' = N + m + 1`,
`N'^{m/2} ∫ (1 + |x|²)^{-N'} H(J(x,1) ι(k)) dx → (∫ e^{-|y|²} dy) H(ι(k))`. -/
theorem tendsto_concentrate {m : ℕ} (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e m)
    {H : Langlands.GeneralLinear (m + 1) ℝ → ℂ} (hH : H ∈ principalSeries ℝ (m + 1) χ)
    {k : Langlands.GeneralLinear m ℝ} (hk : k ∈ unitaryCompact ℝ m) :
    Tendsto (fun N : ℕ => ((Real.sqrt ((N + (m + 1) : ℕ) : ℝ) ^ m : ℝ) : ℂ) *
        ∫ x : Fin m → ℝ, ((((1 + OrthogonalLastRowIntegral.sqNorm x) ^ (N + (m + 1)))⁻¹ : ℝ) : ℂ) *
          H (chartGL x * iotaGL k)) atTop
      (𝓝 ((∫ y : Fin m → ℝ, OrthogonalLastRowIntegral.gaussian y : ℝ) * H (iotaGL k))) := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hH.1.continuous
  have hκ := iotaGL_mem_unitaryCompact hk
  have hNpos : 0 < m + 1 := Nat.succ_pos m
  -- the substituted integrands
  set g : ℕ → (Fin m → ℝ) → ℂ := fun N y =>
    ((((1 + OrthogonalLastRowIntegral.sqNorm y / ((N + (m + 1) : ℕ) : ℝ)) ^ (N + (m + 1)))⁻¹ : ℝ) : ℂ) *
      H (chartGL ((Real.sqrt ((N + (m + 1) : ℕ) : ℝ))⁻¹ • y) * iotaGL k) with hg
  have hsub : ∀ N : ℕ, ((Real.sqrt ((N + (m + 1) : ℕ) : ℝ) ^ m : ℝ) : ℂ) *
      ∫ x : Fin m → ℝ, ((((1 + OrthogonalLastRowIntegral.sqNorm x) ^ (N + (m + 1)))⁻¹ : ℝ) : ℂ) *
        H (chartGL x * iotaGL k) = ∫ y, g N y := by
    intro N
    have hpos : 0 < ((N + (m + 1) : ℕ) : ℝ) := by positivity
    have hsq : 0 < Real.sqrt ((N + (m + 1) : ℕ) : ℝ) := Real.sqrt_pos.mpr hpos
    rw [integral_scale _ hsq]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hg]
    rw [OrthogonalLastRowIntegral.sqNorm_smul, inv_pow, Real.sq_sqrt hpos.le, inv_mul_eq_div]
  refine (tendsto_congr hsub).mpr ?_
  set bound : (Fin m → ℝ) → ℝ := fun y =>
    C * ((1 + OrthogonalLastRowIntegral.sqNorm y / ((m + 1 : ℕ) : ℝ)) ^ (m + 1))⁻¹ with hbound
  have hbi : Integrable bound := (integrable_inv_one_add_div_pow m).const_mul C
  have hlimit : (∫ y : Fin m → ℝ, OrthogonalLastRowIntegral.gaussian y : ℝ) * H (iotaGL k) =
      ∫ y : Fin m → ℝ, ((Real.exp (-OrthogonalLastRowIntegral.sqNorm y) : ℝ) : ℂ) *
        H (iotaGL k) := by
    rw [integral_mul_const, integral_complex_ofReal]
    rfl
  rw [hlimit]
  refine tendsto_integral_of_dominated_convergence bound (fun N => ?_) hbi
    (fun N => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    simp only [hg]
    refine Continuous.mul (Complex.continuous_ofReal.comp (Continuous.inv₀
      ((continuous_const.add (continuous_sqNorm.div_const _)).pow _) fun y => (pow_pos (by
        have := OrthogonalLastRowIntegral.sqNorm_nonneg y
        positivity) _).ne'))
      (hH.1.continuous.comp ((continuous_chartGL.comp (continuous_const_smul _)).mul
        continuous_const))
  · simp only [hg, hbound]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg (by
      have := OrthogonalLastRowIntegral.sqNorm_nonneg y
      positivity) _)), mul_comm C]
    have hs0 := OrthogonalLastRowIntegral.sqNorm_nonneg y
    refine mul_le_mul (inv_anti₀ (pow_pos (by positivity) _)
      (bernoulli_pow hs0 hNpos (by omega))) (norm_chart_le_of_mem hχ he hH hC _ hκ)
      (norm_nonneg _) (inv_nonneg.mpr (pow_nonneg (by positivity) _))
  · simp only [hg]
    have hshift : Tendsto (fun N : ℕ => N + (m + 1)) atTop atTop := tendsto_add_atTop_nat (m + 1)
    have h1 : Tendsto (fun N : ℕ => (1 + OrthogonalLastRowIntegral.sqNorm y /
        ((N + (m + 1) : ℕ) : ℝ)) ^ (N + (m + 1))) atTop (𝓝 (Real.exp (OrthogonalLastRowIntegral.sqNorm y))) :=
      (Real.tendsto_one_add_div_pow_exp _).comp hshift
    have h2 := h1.inv₀ (Real.exp_ne_zero _)
    rw [← Real.exp_neg] at h2
    have h3 : Tendsto (fun N : ℕ => (Real.sqrt ((N + (m + 1) : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
      have h4 : Tendsto (fun N : ℕ => Real.sqrt ((N + (m + 1) : ℕ) : ℝ)) atTop atTop :=
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).comp hshift
      exact tendsto_inv_atTop_zero.comp h4
    have h5 : Tendsto (fun N : ℕ => (Real.sqrt ((N + (m + 1) : ℕ) : ℝ))⁻¹ • y) atTop (𝓝 0) := by
      simpa using h3.smul_const y
    have hcont : Continuous fun z : Fin m → ℝ => H (chartGL z * iotaGL k) :=
      hH.1.continuous.comp (continuous_chartGL.mul continuous_const)
    have h6 := (hcont.tendsto 0).comp h5
    simp only [Function.comp_def, chartGL_zero, one_mul] at h6
    exact ((Complex.continuous_ofReal.tendsto _).comp h2).mul h6

theorem norm_concentrate_le {m : ℕ} (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e m)
    {H : Langlands.GeneralLinear (m + 1) ℝ → ℂ} (hH : H ∈ principalSeries ℝ (m + 1) χ) {C : ℝ}
    (hC : ∀ k ∈ unitaryCompact ℝ (m + 1), ‖H k‖ ≤ C) (N : ℕ)
    {k : Langlands.GeneralLinear m ℝ} (hk : k ∈ unitaryCompact ℝ m) :
    ‖((Real.sqrt ((N + (m + 1) : ℕ) : ℝ) ^ m : ℝ) : ℂ) *
        ∫ x : Fin m → ℝ, ((((1 + OrthogonalLastRowIntegral.sqNorm x) ^ (N + (m + 1)))⁻¹ : ℝ) : ℂ) *
          H (chartGL x * iotaGL k)‖ ≤
      ∫ y : Fin m → ℝ, C * ((1 + OrthogonalLastRowIntegral.sqNorm y / ((m + 1 : ℕ) : ℝ)) ^
        (m + 1))⁻¹ := by
  have hκ := iotaGL_mem_unitaryCompact hk
  have hpos : 0 < ((N + (m + 1) : ℕ) : ℝ) := by positivity
  have hsq : 0 < Real.sqrt ((N + (m + 1) : ℕ) : ℝ) := Real.sqrt_pos.mpr hpos
  rw [integral_scale _ hsq]
  refine norm_integral_le_of_norm_le ((integrable_inv_one_add_div_pow m).const_mul C)
    (ae_of_all _ fun y => ?_)
  have hs0 := OrthogonalLastRowIntegral.sqNorm_nonneg y
  rw [OrthogonalLastRowIntegral.sqNorm_smul, inv_pow, Real.sq_sqrt hpos.le, inv_mul_eq_div,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg (by
      positivity) _)), mul_comm C]
  exact mul_le_mul (inv_anti₀ (pow_pos (by positivity) _)
    (bernoulli_pow hs0 (Nat.succ_pos m) (by omega))) (norm_chart_le_of_mem hχ he hH hC _ hκ)
    (norm_nonneg _) (inv_nonneg.mpr (pow_nonneg (by positivity) _))

/-! ## Nonvanishing -/

theorem shiftChar_neg_one (l : ℕ) : shiftChar χ l (-1) = χ l (-1) := by
  simp [shiftChar]

theorem signVector_zero_one (e : ℕ → ℂ) (p a : ℕ → ℕ) : signVector 0 e p a 1 = 1 := by
  rw [signVector_of_mem p a (unitaryCompact ℝ 0).one_mem]
  simp [signMonomial]

/-- **The Jacquet integral does not vanish.** For strictly dominant signed-power characters
`χ` with signs `χ_l(-1) = (-1)^{p_l}`, some sign vector of the principal series has nonzero
Jacquet integral. -/
theorem exists_jacquet_signVector_ne_zero : ∀ (n : ℕ) {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ},
    IsSignedPower χ e → IsStrictlyDominant e (n - 1) → ∀ {p : ℕ → ℕ},
    (∀ l, χ l (-1) = (-1) ^ p l) → ∃ a : ℕ → ℕ, jacquet n (signVector n e p a) ≠ 0
  | 0, χ, e, _, _, p, _ => ⟨0, by
      change signVector 0 e p 0 1 ≠ 0
      rw [signVector_zero_one]
      exact one_ne_zero⟩
  | m + 1, χ, e, hχ, he, p, hp => by
      have he' : IsStrictlyDominant e m := by simpa using he
      have hp' : ∀ l, shiftChar χ l (-1) = (-1) ^ p l := fun l => by rw [shiftChar_neg_one, hp]
      obtain ⟨a, ha⟩ := exists_jacquet_signVector_ne_zero m hχ.shift
        (isStrictlyDominant_shift he') hp'
      have hH := signVector_mem (n := m + 1) p a hχ hp
      obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hH.1.1.continuous
      set c : ℕ → ℂ := fun N => ((Real.sqrt ((N + (m + 1) : ℕ) : ℝ) ^ m : ℝ) : ℂ) with hcdef
      set F : ℕ → Langlands.GeneralLinear (m + 1) ℝ → ℂ := fun N =>
        c N • signVector (m + 1) e p (bump a m (N + (m + 1))) with hFdef
      have hF : ∀ N, F N ∈ kFiniteFunctions (principalSeries ℝ (m + 1) χ)
          (unitaryCompact ℝ (m + 1)) := fun N =>
        Submodule.smul_mem _ _ (signVector_mem _ _ hχ hp)
      have hval : ∀ N, ∀ k ∈ unitaryCompact ℝ m, jacquetStep (F N) k =
          c N * ∫ x : Fin m → ℝ,
            ((((1 + OrthogonalLastRowIntegral.sqNorm x) ^ (N + (m + 1)))⁻¹ : ℝ) : ℂ) *
              signVector (m + 1) e p a (chartGL x * iotaGL k) := by
        intro N k hk
        simp only [hFdef, jacquetStep, Pi.smul_apply, smul_eq_mul]
        rw [integral_const_mul]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        beta_reduce
        rw [signVector_bump p a hχ hp, qFun_chart x hk]
        push_cast
        rw [inv_pow]
      set cG : ℂ := ((∫ y : Fin m → ℝ, OrthogonalLastRowIntegral.gaussian y : ℝ) : ℂ) with hcG
      have hlim := tendsto_jacquet m hχ.shift (isStrictlyDominant_shift he')
        (f := fun N => jacquetStep (F N)) (f₀ := cG • signVector m (fun l => e l - 1 / 2) p a)
        (fun N => jacquetStep_mem hχ he' (hF N))
        (Submodule.smul_mem _ _ (signVector_mem p a hχ.shift hp'))
        (C := ∫ y : Fin m → ℝ, C * ((1 + OrthogonalLastRowIntegral.sqNorm y /
          ((m + 1 : ℕ) : ℝ)) ^ (m + 1))⁻¹)
        (fun N k hk => by
          rw [hval N k hk]
          exact norm_concentrate_le hχ he' hH.1 hC N hk)
        (fun k hk => by
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [← signVector_iota (e := e) p a (fun l => e l - 1 / 2) hk]
          exact (tendsto_congr fun N => hval N k hk).mpr (tendsto_concentrate hχ he' hH.1 hk))
      have hne : jacquet m (cG • signVector m (fun l => e l - 1 / 2) p a) ≠ 0 := by
        rw [jacquet_smul]
        refine mul_ne_zero ?_ ha
        rw [hcG]
        exact_mod_cast (OrthogonalLastRowIntegral.integral_gaussian_pos (m := m)).ne'
      obtain ⟨N, hN⟩ := (hlim.eventually (isOpen_ne.mem_nhds hne)).exists
      refine ⟨bump a m (N + (m + 1)), fun h0 => hN ?_⟩
      have h1 : jacquet (m + 1) (F N) =
          c N * jacquet (m + 1) (signVector (m + 1) e p (bump a m (N + (m + 1)))) :=
        jacquet_smul _ _ _
      change jacquet (m + 1) (F N) = 0
      rw [h1, h0, mul_zero]

/-- The Jacquet integral is a nonzero functional on the `O(n)`-finite principal series. -/
theorem exists_jacquet_ne_zero {n : ℕ} (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e (n - 1))
    {p : ℕ → ℕ} (hp : ∀ l, χ l (-1) = (-1) ^ p l) :
    ∃ f ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n), jacquet n f ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_jacquet_signVector_ne_zero n hχ he hp
  exact ⟨_, signVector_mem p a hχ hp, ha⟩

end JacquetNonvanishing

end Langlands.Archimedean
