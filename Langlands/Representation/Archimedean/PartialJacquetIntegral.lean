import Langlands.Representation.Archimedean.ParabolicChartBound

/-!
# The partial Jacquet integral along the opposite unipotent radical of `P_{m,1}`
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace PartialJacquet

open MaximalParabolicIntegration ParabolicChartBound GramFormula Langlands.GeneralLinear
  PrincipalSeriesExtension

variable {m : ℕ}

/-! ## Chart identities -/

theorem Jmat_mul_iota (x : Fin m → ℝ) (B : Matrix (Fin m) (Fin m) ℝ) :
    Jmat (Fin.snoc x 1 : Fin (m + 1) → ℝ) * iota B =
      iota B * Jmat (Fin.snoc (x ᵥ* B) 1 : Fin (m + 1) → ℝ) := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Jmat, Matrix.vecMul, dotProduct,
      Matrix.one_apply]

theorem chartGL_mul_iotaGL (x : Fin m → ℝ) (g : Langlands.GeneralLinear m ℝ) :
    chartGL x * iotaGL g = iotaGL g * chartGL (x ᵥ* (g : Matrix (Fin m) (Fin m) ℝ)) := by
  apply Units.ext
  simp only [Units.val_mul, chartGL, JGL_val, iotaGL_val]
  exact Jmat_mul_iota x _

theorem Jmat_mul_dlast (x : Fin m → ℝ) {s : ℝ} (hs : s ≠ 0) :
    Jmat (Fin.snoc x 1 : Fin (m + 1) → ℝ) * dlast s =
      dlast s * Jmat (Fin.snoc (s⁻¹ • x) 1 : Fin (m + 1) → ℝ) := by
  ext i j
  rw [dlast, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Jmat, hs, Matrix.one_apply]

theorem chartGL_mul_dlastGL (x : Fin m → ℝ) (s : ℝˣ) :
    chartGL x * dlastGL s = dlastGL s * chartGL ((s : ℝ)⁻¹ • x) := by
  apply Units.ext
  simp only [Units.val_mul, chartGL, JGL_val, dlastGL_val]
  exact Jmat_mul_dlast x s.ne_zero

theorem chartGL_mul_chartGL_neg (x : Fin m → ℝ) : chartGL x * chartGL (-x) = 1 := by
  apply Units.ext
  simp only [Units.val_mul, chartGL, JGL_val, Units.val_one]
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Jmat, Matrix.one_apply]
  all_goals exact fun h => Fin.castSucc_ne_last _ h.symm

theorem continuous_Jmat_snoc :
    Continuous fun x : Fin m → ℝ => Jmat (Fin.snoc x 1 : Fin (m + 1) → ℝ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp only [Jmat, Matrix.of_apply, Fin.lastCases_last, Fin.snoc_last]
      exact continuous_const
    · simp only [Jmat, Matrix.of_apply, Fin.lastCases_last, Fin.snoc_castSucc]
      exact continuous_apply j'
  · simp only [Jmat, Matrix.of_apply, Fin.lastCases_castSucc]
    exact continuous_const

theorem continuous_chartGL : Continuous (chartGL (m := m)) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : (fun x : Fin m → ℝ => ((chartGL x : Langlands.GeneralLinear (m + 1) ℝ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) =
        fun x => Jmat (Fin.snoc x 1 : Fin (m + 1) → ℝ) := funext fun x => JGL_val _ _
    change Continuous fun x : Fin m → ℝ => ((chartGL x : Langlands.GeneralLinear (m + 1) ℝ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    rw [h]
    exact continuous_Jmat_snoc
  · have h : (fun x : Fin m → ℝ => (((chartGL x)⁻¹ : Langlands.GeneralLinear (m + 1) ℝ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) =
        fun x => Jmat (Fin.snoc (-x) 1 : Fin (m + 1) → ℝ) := funext fun x => by
      rw [inv_eq_of_mul_eq_one_right (chartGL_mul_chartGL_neg x), chartGL, JGL_val]
    rw [h]
    exact continuous_Jmat_snoc.comp continuous_neg

theorem continuous_iotaGL : Continuous (iotaGL (m := m)) := by
  rw [Units.continuous_iff]
  refine ⟨contDiff_iota.continuous.comp Units.continuous_val, ?_⟩
  have h : (fun g : Langlands.GeneralLinear m ℝ => (((iotaGL g)⁻¹ :
      Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) =
      fun g => iota ((g⁻¹ : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) :=
    funext fun g => by rw [← map_inv, iotaGL_val]
  rw [h]
  exact contDiff_iota.continuous.comp Units.continuous_coe_inv

/-! ## Linear changes of variables -/

/-- Right multiplication `x ↦ x B` of row vectors by an invertible matrix, as a linear
equivalence. -/
def vecMulLinearEquiv {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) :
    (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) :=
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  { toFun := fun x => x ᵥ* B
    invFun := fun x => x ᵥ* B⁻¹
    map_add' := fun x y => add_vecMul B x y
    map_smul' := fun c x => by simp [smul_vecMul]
    left_inv := fun x => by simp [vecMul_vecMul, Matrix.mul_nonsing_inv B hBu]
    right_inv := fun x => by simp [vecMul_vecMul, Matrix.nonsing_inv_mul B hBu] }

/-- Right multiplication by an invertible matrix, as a measurable equivalence. -/
def vecMulEquiv {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) : (Fin m → ℝ) ≃ᵐ (Fin m → ℝ) :=
  (LinearEquiv.toContinuousLinearEquiv (vecMulLinearEquiv hB)).toHomeomorph.toMeasurableEquiv

theorem vecMulEquiv_apply {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) (x : Fin m → ℝ) :
    vecMulEquiv hB x = x ᵥ* B := rfl

theorem map_vecMulEquiv {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) :
    Measure.map (vecMulEquiv hB) volume =
      ENNReal.ofReal |B.det⁻¹| • (volume : Measure (Fin m → ℝ)) := by
  have hdet : LinearMap.det ((vecMulLinearEquiv hB : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) :
      (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) = B.det := by
    have : ((vecMulLinearEquiv hB : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) :
        (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) = Matrix.toLin' Bᵀ := by
      apply LinearMap.ext
      intro x
      simp [vecMulLinearEquiv, Matrix.toLin'_apply, mulVec_transpose]
    rw [this, LinearMap.det_toLin', det_transpose]
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin m → ℝ)))
    (f := ((vecMulLinearEquiv hB : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) :
      (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))) (by rw [hdet]; exact hB)
  rw [hdet] at this
  exact this

theorem integral_vecMul_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) (f : (Fin m → ℝ) → E) :
    ∫ x, f (x ᵥ* B) = |B.det|⁻¹ • ∫ x, f x := by
  have h := integral_map_equiv (μ := (volume : Measure (Fin m → ℝ))) (vecMulEquiv hB) f
  rw [map_vecMulEquiv, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at h
  rw [show (∫ x, f (x ᵥ* B)) = ∫ x, f (vecMulEquiv hB x) from rfl, ← h, abs_inv]

theorem integral_vecMul_eq {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0)
    (f : (Fin m → ℝ) → ℂ) :
    ∫ x, f (x ᵥ* B) = ((|B.det|⁻¹ : ℝ) : ℂ) * ∫ x, f x := by
  rw [integral_vecMul_smul hB, Complex.real_smul]

theorem integrable_comp_vecMul {E : Type*} [NormedAddCommGroup E]
    {B : Matrix (Fin m) (Fin m) ℝ} (hB : B.det ≠ 0) {f : (Fin m → ℝ) → E} (hf : Integrable f) :
    Integrable fun x => f (x ᵥ* B) := by
  have h1 : Integrable f (Measure.map (vecMulEquiv hB) volume) := by
    rw [map_vecMulEquiv]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact (integrable_map_equiv (vecMulEquiv hB) f).mp h1

/-! ## Signed-power characters -/

/-- `χ_l(x) = χ_l(sgn x) |x|^{e_l}` for all `l`, with `χ_l(1) = 1` and `‖χ_l(-1)‖ = 1`. -/
structure IsSignedPower (χ : ℕ → ℝˣ → ℂ) (e : ℕ → ℂ) : Prop where
  eq : ∀ (l : ℕ) (x : ℝˣ), χ l x = χ l (signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e l
  one : ∀ l, χ l 1 = 1
  norm_neg_one : ∀ l, ‖χ l (-1)‖ = 1

variable {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

theorem IsSignedPower.norm_sign (hχ : IsSignedPower χ e) (l : ℕ) (x : ℝˣ) :
    ‖χ l (signUnit x)‖ = 1 := by
  unfold signUnit
  split_ifs
  · rw [hχ.one, norm_one]
  · exact hχ.norm_neg_one l

theorem IsSignedPower.norm (hχ : IsSignedPower χ e) (l : ℕ) (x : ℝˣ) :
    ‖χ l x‖ = |(x : ℝ)| ^ (e l).re := by
  rw [hχ.eq, norm_mul, hχ.norm_sign, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr x.ne_zero)]

/-- The pointwise inverse characters. -/
def dualChar (χ : ℕ → ℝˣ → ℂ) (l : ℕ) (x : ℝˣ) : ℂ := (χ l x)⁻¹

theorem IsSignedPower.ne_zero (hχ : IsSignedPower χ e) (l : ℕ) (x : ℝˣ) : χ l x ≠ 0 := by
  rw [← norm_ne_zero_iff, hχ.norm]
  exact (Real.rpow_pos_of_pos (abs_pos.mpr x.ne_zero) _).ne'

theorem IsSignedPower.dual (hχ : IsSignedPower χ e) :
    IsSignedPower (dualChar χ) (fun l => -e l) where
  eq l x := by rw [dualChar, dualChar, hχ.eq l x, mul_inv, Complex.cpow_neg]
  one l := by simp [dualChar, hχ.one]
  norm_neg_one l := by simp [dualChar, hχ.norm_neg_one]

theorem norm_principalSeriesCharacter (hχ : IsSignedPower χ e) (N : ℕ) (a : Fin N → ℝˣ) :
    ‖principalSeriesCharacter ℝ N χ a‖ =
      ∏ l : Fin N, |(a l : ℝ)| ^ ((e l).re + ((N : ℝ) - 1) / 2 - (l : ℕ)) := by
  rw [principalSeriesCharacter, norm_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  have ha : 0 < |(a l : ℝ)| := abs_pos.mpr (a l).ne_zero
  rw [norm_mul, hχ.norm, Module.finrank_self, pow_one, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos ha, ← Real.rpow_add ha]
  congr 1
  simp only [Complex.sub_re, Complex.div_re, Complex.natCast_re, Complex.one_re,
    Complex.natCast_im, Complex.one_im, Complex.sub_im]
  norm_num
  ring

/-- The exponent `σ_l = Re e_l + (N-1)/2 - l` of `‖χδ^{1/2}‖`. -/
def normExponent (e : ℕ → ℂ) (N : ℕ) (l : ℕ) : ℝ := (e l).re + ((N : ℝ) - 1) / 2 - l

/-- The exponent `ε_l = (Re e_{l+1} - Re e_l - 1)/2` of the chart bound. -/
def chartExponent (e : ℕ → ℂ) (l : Fin m) : ℝ := ((e ((l : ℕ) + 1)).re - (e l).re - 1) / 2

/-- Strictly decreasing real parts of `e_0, …, e_m`. -/
def IsStrictlyDominant (e : ℕ → ℂ) (m : ℕ) : Prop :=
  ∀ l : ℕ, l < m → (e (l + 1)).re < (e l).re

theorem chartExponent_lt (he : IsStrictlyDominant e m) (l : Fin m) :
    chartExponent e l < -1 / 2 := by
  have := he l l.isLt
  unfold chartExponent
  linarith

theorem exists_bound_unitaryCompact {n : ℕ} {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : Continuous f) : ∃ C, ∀ k ∈ unitaryCompact ℝ n, ‖f k‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((hf.comp continuous_subtype_val : Continuous fun k : unitaryCompact ℝ n => f k).continuousOn)
  exact ⟨C, fun k hk => hC ⟨k, hk⟩ trivial⟩

variable {h : Langlands.GeneralLinear (m + 1) ℝ → ℂ}

/-- The chart bound for a function of the principal series of signed-power characters. -/
theorem norm_le_partialSq (hχ : IsSignedPower χ e) (hh : h ∈ principalSeries ℝ (m + 1) χ)
    {C : ℝ} (hC : ∀ k ∈ unitaryCompact ℝ (m + 1), ‖h k‖ ≤ C) (x : Fin m → ℝ)
    {κ : Langlands.GeneralLinear (m + 1) ℝ} (hκ : κ ∈ unitaryCompact ℝ (m + 1)) :
    ‖h (chartGL x * κ)‖ ≤ C * ∏ l : Fin m, partialSq x ((l : ℕ) + 1) ^ chartExponent e l := by
  have hb := norm_le_chart (σ := normExponent e (m + 1)) hh.2
    (fun a => by rw [norm_principalSeriesCharacter hχ]; rfl) hC x hκ
  have hexp : ∀ l : Fin m, (normExponent e (m + 1) ((l : ℕ) + 1) -
      normExponent e (m + 1) l) / 2 = chartExponent e l := by
    intro l
    unfold normExponent chartExponent
    push_cast
    ring
  simp only [hexp] at hb
  exact hb

/-- The chart bound for a function of the principal series, for strictly dominant exponents. -/
theorem norm_le_of_mem_principalSeries (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e m)
    (hh : h ∈ principalSeries ℝ (m + 1) χ) {C : ℝ}
    (hC : ∀ k ∈ unitaryCompact ℝ (m + 1), ‖h k‖ ≤ C) (x : Fin m → ℝ)
    {κ : Langlands.GeneralLinear (m + 1) ℝ} (hκ : κ ∈ unitaryCompact ℝ (m + 1)) :
    ‖h (chartGL x * κ)‖ ≤ C * ∏ l : Fin m, (1 + x l ^ 2) ^ chartExponent e l := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1 (unitaryCompact ℝ (m + 1)).one_mem)
  refine (norm_le_partialSq hχ hh hC x hκ).trans (mul_le_mul_of_nonneg_left ?_ hC0)
  exact prod_partialSq_rpow_le fun l => by
    have := chartExponent_lt he l
    linarith

theorem integrable_chart (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e m)
    (hh : h ∈ principalSeries ℝ (m + 1) χ) {κ : Langlands.GeneralLinear (m + 1) ℝ}
    (hκ : κ ∈ unitaryCompact ℝ (m + 1)) :
    Integrable fun x : Fin m → ℝ => h (chartGL x * κ) := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hh.1.continuous
  refine Integrable.mono' ((integrable_prod_one_add_sq_rpow (chartExponent_lt he)).const_mul C)
    ((hh.1.continuous.comp (continuous_chartGL.mul continuous_const)).aestronglyMeasurable)
    (ae_of_all _ fun x => norm_le_of_mem_principalSeries hχ he hh hC x hκ)

/-! ## The partial Jacquet integral -/

/-- `T h(g) = ∫_{ℝ^m} h(J(x,1) ι(g)) dx`. -/
def jacquetStep (h : Langlands.GeneralLinear (m + 1) ℝ → ℂ) (g : Langlands.GeneralLinear m ℝ) :
    ℂ :=
  ∫ x : Fin m → ℝ, h (chartGL x * iotaGL g)

theorem continuous_jacquetStep_unitary (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e m)
    (hh : h ∈ principalSeries ℝ (m + 1) χ) :
    Continuous fun κ : Matrix.unitaryGroup (Fin m) ℝ => jacquetStep h (Unitary.toUnits κ) := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hh.1.continuous
  refine continuous_of_dominated (bound := fun x => C * ∏ l : Fin m, (1 + x l ^ 2) ^
    chartExponent e l) (fun κ => ?_) (fun κ => ae_of_all _ fun x => ?_)
    ((integrable_prod_one_add_sq_rpow (chartExponent_lt he)).const_mul C)
    (ae_of_all _ fun x => ?_)
  · exact (hh.1.continuous.comp (continuous_chartGL.mul continuous_const)).aestronglyMeasurable
  · exact norm_le_of_mem_principalSeries hχ he hh hC x
      (iotaGL_mem_unitaryCompact (k := Unitary.toUnits κ) κ.2)
  · exact hh.1.continuous.comp (continuous_const.mul
      (continuous_iotaGL.comp continuous_unitary_toUnits))

/-! ## Equivariance -/

/-- The shifted characters `χ''_l(x) = χ_l(x) |x|^{-1/2}`. -/
def shiftChar (χ : ℕ → ℝˣ → ℂ) (l : ℕ) (x : ℝˣ) : ℂ :=
  χ l x * ((|(x : ℝ)| : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))

theorem IsSignedPower.shift (hχ : IsSignedPower χ e) :
    IsSignedPower (shiftChar χ) (fun l => e l - 1 / 2) where
  eq l x := by
    have hx : ((|(x : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr x.ne_zero
    rw [shiftChar, shiftChar, hχ.eq l x, abs_signUnit, Complex.ofReal_one, Complex.one_cpow,
      mul_one, mul_assoc, ← Complex.cpow_add _ _ hx]
    congr 2
  one l := by simp [shiftChar, hχ.one]
  norm_neg_one l := by simp [shiftChar, hχ.norm_neg_one]

theorem IsStrictlyDominant.shift (he : IsStrictlyDominant e (m + 1)) :
    IsStrictlyDominant (fun l => e l - 1 / 2) m := by
  intro l hl
  have := he l (by omega)
  simp only [Complex.sub_re]
  linarith

theorem principalSeriesCharacter_lastCases (hχ1 : χ m 1 = 1) (a : Fin m → ℝˣ) :
    principalSeriesCharacter ℝ (m + 1) χ (fun i => Fin.lastCases 1 a i) *
        (((∏ i, |(a i : ℝ)|)⁻¹ : ℝ) : ℂ) =
      principalSeriesCharacter ℝ m (shiftChar χ) a := by
  rw [principalSeriesCharacter, principalSeriesCharacter, Fin.prod_univ_castSucc]
  simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.val_castSucc, Fin.val_last, hχ1,
    Units.val_one, norm_one, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one]
  rw [Complex.ofReal_inv, Complex.ofReal_prod, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [shiftChar]
  simp only [Module.finrank_self, pow_one, Real.norm_eq_abs]
  have hx : ((|(a i : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr (a i).ne_zero
  rw [← Complex.cpow_neg_one, mul_assoc, mul_assoc, ← Complex.cpow_add _ _ hx,
    ← Complex.cpow_add _ _ hx]
  congr 2
  push_cast
  ring

theorem jacquetStep_mul (hh : h ∈ principalSeries ℝ (m + 1) χ) (hχ1 : χ m 1 = 1)
    (a : Fin m → ℝˣ) (u : upperUnipotent m ℝ) (g : Langlands.GeneralLinear m ℝ) :
    jacquetStep h ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear m ℝ) *
        (u : Langlands.GeneralLinear m ℝ) * g) =
      principalSeriesCharacter ℝ m (shiftChar χ) a * jacquetStep h g := by
  set b : Langlands.GeneralLinear m ℝ :=
    (Iwasawa.diagonalUnits a : Langlands.GeneralLinear m ℝ) * (u : Langlands.GeneralLinear m ℝ)
    with hbdef
  have hdet : ((b : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ).det =
      ∏ i, (a i : ℝ) := by
    rw [hbdef, Units.val_mul, Matrix.det_mul, det_upperUnipotent u, mul_one,
      Iwasawa.diagonalUnits_val, Matrix.det_diagonal]
  have hdet0 : ((b : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ).det ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (a i).ne_zero
  have hpt : ∀ x : Fin m → ℝ, h (chartGL x * iotaGL (b * g)) =
      principalSeriesCharacter ℝ (m + 1) χ (fun i => Fin.lastCases 1 a i) *
        h (chartGL (x ᵥ* ((b : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ)) *
          iotaGL g) := by
    intro x
    rw [map_mul, ← mul_assoc, chartGL_mul_iotaGL, mul_assoc]
    have hb : iotaGL b = (Iwasawa.diagonalUnits (fun i => Fin.lastCases 1 a i) :
        Langlands.GeneralLinear (m + 1) ℝ) *
        ((⟨iotaGL (u : Langlands.GeneralLinear m ℝ), iotaGL_mem_upperUnipotent u⟩ :
          upperUnipotent (m + 1) ℝ) : Langlands.GeneralLinear (m + 1) ℝ) := by
      rw [hbdef, map_mul, iotaGL_diagonalUnits]
    rw [hb]
    exact hh.2 _ _ _
  unfold jacquetStep
  rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul,
    integral_vecMul_eq hdet0 (fun y => h (chartGL y * iotaGL g)), ← mul_assoc, hdet,
    Finset.abs_prod, principalSeriesCharacter_lastCases hχ1]

/-! ## Finiteness under `O(m)` -/

theorem jacquetStep_rightTranslation (f : Langlands.GeneralLinear (m + 1) ℝ → ℂ)
    (g k : Langlands.GeneralLinear m ℝ) :
    jacquetStep (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (m + 1) ℝ) (iotaGL k) f) g =
      jacquetStep f (g * k) := by
  unfold jacquetStep
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  change f (chartGL x * iotaGL g * iotaGL k) = f (chartGL x * iotaGL (g * k))
  rw [map_mul, mul_assoc]

/-- The partial Jacquet integral restricted to `O(m)`, as a linear map on a submodule of the
principal series. -/
def jacquetStepOn (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e m)
    (V : Submodule ℂ (Langlands.GeneralLinear (m + 1) ℝ → ℂ))
    (hV : V ≤ principalSeries ℝ (m + 1) χ) :
    V →ₗ[ℂ] (Matrix.unitaryGroup (Fin m) ℝ → ℂ) where
  toFun f κ := jacquetStep (f : Langlands.GeneralLinear (m + 1) ℝ → ℂ) (Unitary.toUnits κ)
  map_add' f g := funext fun κ => by
    have hκ : iotaGL (Unitary.toUnits κ) ∈ unitaryCompact ℝ (m + 1) :=
      iotaGL_mem_unitaryCompact (k := Unitary.toUnits κ) κ.2
    simp only [jacquetStep, Submodule.coe_add, Pi.add_apply]
    exact integral_add (integrable_chart hχ he (hV f.2) hκ) (integrable_chart hχ he (hV g.2) hκ)
  map_smul' c f := funext fun κ => by
    simp only [jacquetStep, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

theorem finiteDimensional_jacquetStep (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e m)
    (hh : h ∈ kFiniteFunctions (principalSeries ℝ (m + 1) χ) (unitaryCompact ℝ (m + 1))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin m) ℝ =>
      fun x : Matrix.unitaryGroup (Fin m) ℝ => jacquetStep h (Unitary.toUnits (x * k)))) := by
  set V := Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ (m + 1) =>
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (m + 1) ℝ)
      (k : Langlands.GeneralLinear (m + 1) ℝ) h) with hVdef
  have hVfin : FiniteDimensional ℂ V := (mem_kFiniteVectors_iff _ _ _).mp hh.2
  have hV : V ≤ principalSeries ℝ (m + 1) χ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact rightTranslation_mem_principalSeries (χ := χ) hh.1 _
  have hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin m) ℝ =>
      fun x : Matrix.unitaryGroup (Fin m) ℝ => jacquetStep h (Unitary.toUnits (x * k))) ≤
      LinearMap.range (jacquetStepOn hχ he V hV) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    have hk : iotaGL (Unitary.toUnits k) ∈ unitaryCompact ℝ (m + 1) :=
      iotaGL_mem_unitaryCompact (k := Unitary.toUnits k) k.2
    refine ⟨⟨_, Submodule.subset_span ⟨⟨_, hk⟩, rfl⟩⟩, funext fun x => ?_⟩
    change jacquetStep _ (Unitary.toUnits x) = jacquetStep h (Unitary.toUnits (x * k))
    rw [jacquetStep_rightTranslation, map_mul]
  exact Submodule.finiteDimensional_of_le hle

/-! ## The partial Jacquet integral lies in the shifted principal series -/

theorem signDiagonal_toUnits (a : Fin m → ℝˣ) (κ : Matrix.unitaryGroup (Fin m) ℝ) :
    Unitary.toUnits (signDiagonal (fun i => (a i : ℝ)) * κ) =
      (Iwasawa.diagonalUnits (fun i => signUnit (a i)) : Langlands.GeneralLinear m ℝ) *
        ((1 : upperUnipotent m ℝ) : Langlands.GeneralLinear m ℝ) * Unitary.toUnits κ := by
  apply Units.ext
  simp only [map_mul, Units.val_mul, OneMemClass.coe_one, mul_one,
    Iwasawa.diagonalUnits_val]
  congr 1
  change Matrix.diagonal (fun i => signReal (a i : ℝ)) = _
  congr 1
  funext i
  unfold signReal signUnit
  split_ifs <;> simp

/-- **The partial Jacquet integral.** For strictly dominant signed-power characters, the
partial Jacquet integral of an `O(m+1)`-finite function of the principal series of `χ` on
`GL_{m+1}(ℝ)` is an `O(m)`-finite function of the principal series of `χ |·|^{-1/2}` on
`GL_m(ℝ)`. -/
theorem jacquetStep_mem (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e m)
    (hh : h ∈ kFiniteFunctions (principalSeries ℝ (m + 1) χ) (unitaryCompact ℝ (m + 1))) :
    jacquetStep h ∈ kFiniteFunctions (principalSeries ℝ m (shiftChar χ)) (unitaryCompact ℝ m) := by
  set φ : Matrix.unitaryGroup (Fin m) ℝ → ℂ := fun κ => jacquetStep h (Unitary.toUnits κ)
    with hφdef
  have hφc : Continuous φ := continuous_jacquetStep_unitary hχ he hh.1
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin m) ℝ => fun x => φ (x * k))) :=
    finiteDimensional_jacquetStep hχ he hh
  have hφM : ∀ (a : Fin m → ℝˣ) (κ : Matrix.unitaryGroup (Fin m) ℝ),
      φ (signDiagonal (fun i => (a i : ℝ)) * κ) =
        principalSeriesCharacter ℝ m (shiftChar χ) (fun i => signUnit (a i)) * φ κ := by
    intro a κ
    simp only [hφdef]
    rw [signDiagonal_toUnits, jacquetStep_mul hh.1 (hχ.one m)]
  have hE := extension_mem_kFiniteFunctions (fun l => e l - 1 / 2) hχ.shift.eq hφc hfin hφM
  convert hE using 1
  funext g
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  rw [jacquetStep_mul hh.1 (hχ.one m), hE.1.2 a u k]
  congr 1
  have hku : k = Unitary.toUnits (⟨(k : Matrix (Fin m) (Fin m) ℝ), hk⟩ :
      Matrix.unitaryGroup (Fin m) ℝ) := Units.ext rfl
  rw [hku, extension_unitary]

end PartialJacquet

end Langlands.Archimedean
