import Langlands.Representation.Archimedean.ComplexParabolicChartBound
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesExtension

/-!
# The partial Jacquet integral along the opposite unipotent radical of `P_{m,1}` of `GL_{m+1}(ℂ)`

For `h` a `U(m+1)`-finite function of the principal series of strictly dominant characters `χ` of
`GL_{m+1}(ℂ)`, the partial Jacquet integral `T h(g) = ∫_{ℂ^m} h(J(x,1) ι(g)) dx` converges and is a
`U(m)`-finite function of the principal series of `χ |·|_ℂ^{-1/2}` on `GL_m(ℂ)`
(`ComplexPartialJacquet.jacquetStep_mem`).
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator ComplexConjugate

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexPartialJacquet

open ComplexMaximalParabolicIntegration ComplexParabolicChartBound ComplexGramFormula
  Langlands.GeneralLinear ComplexPrincipalSeriesExtension

variable {m : ℕ}

/-! ## Chart identities -/

theorem Jmat_mul_iota (x : Fin m → ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    Jmat (Fin.snoc x 1 : Fin (m + 1) → ℂ) * iota B =
      iota B * Jmat (Fin.snoc (x ᵥ* B) 1 : Fin (m + 1) → ℂ) := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Jmat, Matrix.vecMul, dotProduct,
      Matrix.one_apply]

theorem chartGL_mul_iotaGL (x : Fin m → ℂ) (g : Langlands.GeneralLinear m ℂ) :
    chartGL x * iotaGL g = iotaGL g * chartGL (x ᵥ* (g : Matrix (Fin m) (Fin m) ℂ)) := by
  apply Units.ext
  simp only [Units.val_mul, chartGL, JGL_val, iotaGL_val]
  exact Jmat_mul_iota x _

theorem Jmat_mul_dlast (x : Fin m → ℂ) {s : ℂ} (hs : s ≠ 0) :
    Jmat (Fin.snoc x 1 : Fin (m + 1) → ℂ) * dlast s =
      dlast s * Jmat (Fin.snoc (s⁻¹ • x) 1 : Fin (m + 1) → ℂ) := by
  ext i j
  rw [dlast, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Jmat, hs, Matrix.one_apply]

theorem chartGL_mul_dlastGL (x : Fin m → ℂ) (s : ℂˣ) :
    chartGL x * dlastGL s = dlastGL s * chartGL ((s : ℂ)⁻¹ • x) := by
  apply Units.ext
  simp only [Units.val_mul, chartGL, JGL_val, dlastGL_val]
  exact Jmat_mul_dlast x s.ne_zero

theorem chartGL_mul_chartGL_neg (x : Fin m → ℂ) : chartGL x * chartGL (-x) = 1 := by
  apply Units.ext
  simp only [Units.val_mul, chartGL, JGL_val, Units.val_one]
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Jmat, Matrix.one_apply]
  all_goals exact fun h => Fin.castSucc_ne_last _ h.symm

theorem continuous_Jmat_snoc :
    Continuous fun x : Fin m → ℂ => Jmat (Fin.snoc x 1 : Fin (m + 1) → ℂ) := by
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
  · have h : (fun x : Fin m → ℂ => ((chartGL x : Langlands.GeneralLinear (m + 1) ℂ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) =
        fun x => Jmat (Fin.snoc x 1 : Fin (m + 1) → ℂ) := funext fun x => JGL_val _ _
    change Continuous fun x : Fin m → ℂ => ((chartGL x : Langlands.GeneralLinear (m + 1) ℂ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    rw [h]
    exact continuous_Jmat_snoc
  · have h : (fun x : Fin m → ℂ => (((chartGL x)⁻¹ : Langlands.GeneralLinear (m + 1) ℂ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) =
        fun x => Jmat (Fin.snoc (-x) 1 : Fin (m + 1) → ℂ) := funext fun x => by
      rw [inv_eq_of_mul_eq_one_right (chartGL_mul_chartGL_neg x), chartGL, JGL_val]
    rw [h]
    exact continuous_Jmat_snoc.comp continuous_neg

theorem continuous_iotaGL : Continuous (iotaGL (m := m)) := by
  rw [Units.continuous_iff]
  refine ⟨contDiff_iota.continuous.comp Units.continuous_val, ?_⟩
  have h : (fun g : Langlands.GeneralLinear m ℂ => (((iotaGL g)⁻¹ :
      Langlands.GeneralLinear (m + 1) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) =
      fun g => iota ((g⁻¹ : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) :=
    funext fun g => by rw [← map_inv, iotaGL_val]
  rw [h]
  exact contDiff_iota.continuous.comp Units.continuous_coe_inv

/-! ## Linear changes of variables -/

/-- Right multiplication `x ↦ x B` of row vectors by an invertible matrix, as a linear
equivalence. -/
def vecMulLinearEquiv {B : Matrix (Fin m) (Fin m) ℂ} (hB : B.det ≠ 0) :
    (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ) :=
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  { toFun := fun x => x ᵥ* B
    invFun := fun x => x ᵥ* B⁻¹
    map_add' := fun x y => add_vecMul B x y
    map_smul' := fun c x => by simp [smul_vecMul]
    left_inv := fun x => by simp [vecMul_vecMul, Matrix.mul_nonsing_inv B hBu]
    right_inv := fun x => by simp [vecMul_vecMul, Matrix.nonsing_inv_mul B hBu] }

theorem det_vecMulLinearEquiv {B : Matrix (Fin m) (Fin m) ℂ} (hB : B.det ≠ 0) :
    LinearMap.det ((vecMulLinearEquiv hB : (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ)) :
      (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) = B.det := by
  have : ((vecMulLinearEquiv hB : (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ)) :
      (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) = Matrix.toLin' Bᵀ := by
    apply LinearMap.ext
    intro x
    simp [vecMulLinearEquiv, Matrix.toLin'_apply, mulVec_transpose]
  rw [this, LinearMap.det_toLin', det_transpose]

/-- Right multiplication by an invertible matrix, as a measurable equivalence. -/
def vecMulEquiv {B : Matrix (Fin m) (Fin m) ℂ} (hB : B.det ≠ 0) : (Fin m → ℂ) ≃ᵐ (Fin m → ℂ) :=
  (LinearEquiv.toContinuousLinearEquiv
    ((vecMulLinearEquiv hB).restrictScalars ℝ)).toHomeomorph.toMeasurableEquiv

theorem vecMulEquiv_apply {B : Matrix (Fin m) (Fin m) ℂ} (hB : B.det ≠ 0) (x : Fin m → ℂ) :
    vecMulEquiv hB x = x ᵥ* B := rfl

/-- Lebesgue measure on `ℂ^m` transforms under `x ↦ x B` by `|det B|⁻²`. -/
theorem map_vecMulEquiv {B : Matrix (Fin m) (Fin m) ℂ} (hB : B.det ≠ 0) :
    Measure.map (vecMulEquiv hB) volume =
      ENNReal.ofReal ((‖B.det‖ ^ 2)⁻¹) • (volume : Measure (Fin m → ℂ)) := by
  set Lr : (Fin m → ℂ) ≃ₗ[ℝ] (Fin m → ℂ) := (vecMulLinearEquiv hB).restrictScalars ℝ
  have hdet : LinearMap.det (Lr : (Fin m → ℂ) →ₗ[ℝ] (Fin m → ℂ)) = Complex.normSq B.det := by
    have := LinearMap.det_restrictScalars (R := ℝ) (S := ℂ) (A := Fin m → ℂ)
      (f := ((vecMulLinearEquiv hB : (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ)) :
        (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)))
    rw [Algebra.norm_complex_apply, det_vecMulLinearEquiv] at this
    exact this
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin m → ℂ)))
    (f := (Lr : (Fin m → ℂ) →ₗ[ℝ] (Fin m → ℂ)))
    (by rw [hdet]; exact (Complex.normSq_pos.mpr hB).ne')
  rw [hdet, Complex.normSq_eq_norm_sq, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))] at this
  exact this

theorem integral_vecMul_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : Matrix (Fin m) (Fin m) ℂ} (hB : B.det ≠ 0) (f : (Fin m → ℂ) → E) :
    ∫ x, f (x ᵥ* B) = (‖B.det‖ ^ 2)⁻¹ • ∫ x, f x := by
  have h := integral_map_equiv (μ := (volume : Measure (Fin m → ℂ))) (vecMulEquiv hB) f
  rw [map_vecMulEquiv, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg _))] at h
  rw [show (∫ x, f (x ᵥ* B)) = ∫ x, f (vecMulEquiv hB x) from rfl, ← h]

theorem integral_vecMul_eq {B : Matrix (Fin m) (Fin m) ℂ} (hB : B.det ≠ 0)
    (f : (Fin m → ℂ) → ℂ) :
    ∫ x, f (x ᵥ* B) = (((‖B.det‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∫ x, f x := by
  rw [integral_vecMul_smul hB, Complex.real_smul]

theorem integrable_comp_vecMul {E : Type*} [NormedAddCommGroup E]
    {B : Matrix (Fin m) (Fin m) ℂ} (hB : B.det ≠ 0) {f : (Fin m → ℂ) → E} (hf : Integrable f) :
    Integrable fun x => f (x ᵥ* B) := by
  have h1 : Integrable f (Measure.map (vecMulEquiv hB) volume) := by
    rw [map_vecMulEquiv]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact (integrable_map_equiv (vecMulEquiv hB) f).mp h1

/-! ## Phase-power characters -/

/-- `χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}` for all `l`, with `χ_l(1) = 1` and `|χ_l| = 1` on phases. -/
structure IsPhasePower (χ : ℕ → ℂˣ → ℂ) (e : ℕ → ℂ) : Prop where
  eq : ∀ (l : ℕ) (z : ℂˣ), χ l z = χ l (phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l
  one : ∀ l, χ l 1 = 1
  norm_phase : ∀ (l : ℕ) (z : ℂˣ), ‖χ l (phaseUnit z)‖ = 1

variable {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

theorem IsPhasePower.norm (hχ : IsPhasePower χ e) (l : ℕ) (z : ℂˣ) :
    ‖χ l z‖ = ‖(z : ℂ)‖ ^ (2 * (e l).re) := by
  have hz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  rw [hχ.eq, norm_mul, hχ.norm_phase, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (pow_pos hz 2), ← Real.rpow_natCast,
    ← Real.rpow_mul hz.le]
  norm_num

/-- The pointwise inverse characters. -/
def dualChar (χ : ℕ → ℂˣ → ℂ) (l : ℕ) (z : ℂˣ) : ℂ := (χ l z)⁻¹

theorem IsPhasePower.ne_zero (hχ : IsPhasePower χ e) (l : ℕ) (z : ℂˣ) : χ l z ≠ 0 := by
  rw [← norm_ne_zero_iff, hχ.norm]
  exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr z.ne_zero) _).ne'

theorem IsPhasePower.dual (hχ : IsPhasePower χ e) :
    IsPhasePower (dualChar χ) (fun l => -e l) where
  eq l z := by rw [dualChar, dualChar, hχ.eq l z, mul_inv, Complex.cpow_neg]
  one l := by simp [dualChar, hχ.one]
  norm_phase l z := by simp [dualChar, hχ.norm_phase]

theorem norm_principalSeriesCharacter (hχ : IsPhasePower χ e) (N : ℕ) (a : Fin N → ℂˣ) :
    ‖principalSeriesCharacter ℂ N χ a‖ =
      ∏ l : Fin N, ‖(a l : ℂ)‖ ^ (2 * ((e l).re + ((N : ℝ) - 1) / 2 - (l : ℕ))) := by
  rw [principalSeriesCharacter, norm_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  have ha : 0 < ‖(a l : ℂ)‖ := norm_pos_iff.mpr (a l).ne_zero
  rw [norm_mul, hχ.norm, Complex.finrank_real_complex,
    Complex.norm_cpow_eq_rpow_re_of_pos (pow_pos ha 2), ← Real.rpow_natCast,
    ← Real.rpow_mul ha.le, ← Real.rpow_add ha]
  congr 1
  simp only [Complex.sub_re, Complex.div_re, Complex.natCast_re, Complex.one_re,
    Complex.natCast_im, Complex.one_im, Complex.sub_im]
  norm_num
  ring

/-- The exponent `σ_l = 2 (Re e_l + (N-1)/2 - l)` of `‖χ δ^{1/2}‖`. -/
def normExponent (e : ℕ → ℂ) (N : ℕ) (l : ℕ) : ℝ := 2 * ((e l).re + ((N : ℝ) - 1) / 2 - l)

/-- The exponent `ε_l = Re e_{l+1} - Re e_l - 1` of the chart bound. -/
def chartExponent (e : ℕ → ℂ) (l : Fin m) : ℝ := (e ((l : ℕ) + 1)).re - (e l).re - 1

/-- Strictly decreasing real parts of `e_0, …, e_m`. -/
def IsStrictlyDominant (e : ℕ → ℂ) (m : ℕ) : Prop :=
  ∀ l : ℕ, l < m → (e (l + 1)).re < (e l).re

theorem chartExponent_lt (he : IsStrictlyDominant e m) (l : Fin m) :
    chartExponent e l < -1 := by
  have := he l l.isLt
  unfold chartExponent
  linarith

theorem exists_bound_unitaryCompact {n : ℕ} {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : Continuous f) : ∃ C, ∀ k ∈ unitaryCompact ℂ n, ‖f k‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((hf.comp continuous_subtype_val : Continuous fun k : unitaryCompact ℂ n => f k).continuousOn)
  exact ⟨C, fun k hk => hC ⟨k, hk⟩ trivial⟩

variable {h : Langlands.GeneralLinear (m + 1) ℂ → ℂ}

/-- The chart bound for a function of the principal series of phase-power characters. -/
theorem norm_le_partialSq (hχ : IsPhasePower χ e) (hh : h ∈ principalSeries ℂ (m + 1) χ)
    {C : ℝ} (hC : ∀ k ∈ unitaryCompact ℂ (m + 1), ‖h k‖ ≤ C) (x : Fin m → ℂ)
    {κ : Langlands.GeneralLinear (m + 1) ℂ} (hκ : κ ∈ unitaryCompact ℂ (m + 1)) :
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
theorem norm_le_of_mem_principalSeries (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e m)
    (hh : h ∈ principalSeries ℂ (m + 1) χ) {C : ℝ}
    (hC : ∀ k ∈ unitaryCompact ℂ (m + 1), ‖h k‖ ≤ C) (x : Fin m → ℂ)
    {κ : Langlands.GeneralLinear (m + 1) ℂ} (hκ : κ ∈ unitaryCompact ℂ (m + 1)) :
    ‖h (chartGL x * κ)‖ ≤ C * ∏ l : Fin m, (1 + ‖x l‖ ^ 2) ^ chartExponent e l := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1 (unitaryCompact ℂ (m + 1)).one_mem)
  refine (norm_le_partialSq hχ hh hC x hκ).trans (mul_le_mul_of_nonneg_left ?_ hC0)
  exact prod_partialSq_rpow_le fun l => by
    have := chartExponent_lt he l
    linarith

theorem integrable_chart (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e m)
    (hh : h ∈ principalSeries ℂ (m + 1) χ) {κ : Langlands.GeneralLinear (m + 1) ℂ}
    (hκ : κ ∈ unitaryCompact ℂ (m + 1)) :
    Integrable fun x : Fin m → ℂ => h (chartGL x * κ) := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hh.1.continuous
  refine Integrable.mono' ((integrable_prod_one_add_sq_rpow (chartExponent_lt he)).const_mul C)
    ((hh.1.continuous.comp (continuous_chartGL.mul continuous_const)).aestronglyMeasurable)
    (ae_of_all _ fun x => norm_le_of_mem_principalSeries hχ he hh hC x hκ)

/-! ## The partial Jacquet integral -/

/-- `T h(g) = ∫_{ℂ^m} h(J(x,1) ι(g)) dx`. -/
def jacquetStep (h : Langlands.GeneralLinear (m + 1) ℂ → ℂ) (g : Langlands.GeneralLinear m ℂ) :
    ℂ :=
  ∫ x : Fin m → ℂ, h (chartGL x * iotaGL g)

theorem continuous_jacquetStep_unitary (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e m)
    (hh : h ∈ principalSeries ℂ (m + 1) χ) :
    Continuous fun κ : Matrix.unitaryGroup (Fin m) ℂ => jacquetStep h (Unitary.toUnits κ) := by
  obtain ⟨C, hC⟩ := exists_bound_unitaryCompact hh.1.continuous
  refine continuous_of_dominated (bound := fun x => C * ∏ l : Fin m, (1 + ‖x l‖ ^ 2) ^
    chartExponent e l) (fun κ => ?_) (fun κ => ae_of_all _ fun x => ?_)
    ((integrable_prod_one_add_sq_rpow (chartExponent_lt he)).const_mul C)
    (ae_of_all _ fun x => ?_)
  · exact (hh.1.continuous.comp (continuous_chartGL.mul continuous_const)).aestronglyMeasurable
  · exact norm_le_of_mem_principalSeries hχ he hh hC x
      (iotaGL_mem_unitaryCompact (k := Unitary.toUnits κ) κ.2)
  · exact hh.1.continuous.comp (continuous_const.mul
      (continuous_iotaGL.comp continuous_unitary_toUnits))

/-! ## Equivariance -/

/-- The shifted characters `χ''_l(z) = χ_l(z) (|z|²)^{-1/2}`. -/
def shiftChar (χ : ℕ → ℂˣ → ℂ) (l : ℕ) (z : ℂˣ) : ℂ :=
  χ l z * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))

theorem IsPhasePower.shift (hχ : IsPhasePower χ e) :
    IsPhasePower (shiftChar χ) (fun l => e l - 1 / 2) where
  eq l z := by
    have hz : ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr z.ne_zero)
    rw [shiftChar, shiftChar, hχ.eq l z, norm_phaseUnit, one_pow, Complex.ofReal_one,
      Complex.one_cpow, mul_one, mul_assoc, ← Complex.cpow_add _ _ hz]
    congr 2
  one l := by simp [shiftChar, hχ.one]
  norm_phase l z := by simp [shiftChar, hχ.norm_phase, norm_phaseUnit]

theorem IsStrictlyDominant.shift (he : IsStrictlyDominant e (m + 1)) :
    IsStrictlyDominant (fun l => e l - 1 / 2) m := by
  intro l hl
  have := he l (by omega)
  simp only [Complex.sub_re]
  linarith

theorem principalSeriesCharacter_lastCases (hχ1 : χ m 1 = 1) (a : Fin m → ℂˣ) :
    principalSeriesCharacter ℂ (m + 1) χ (fun i => Fin.lastCases 1 a i) *
        (((∏ i, ‖(a i : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ) =
      principalSeriesCharacter ℂ m (shiftChar χ) a := by
  rw [principalSeriesCharacter, principalSeriesCharacter, Fin.prod_univ_castSucc]
  simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.val_castSucc, Fin.val_last, hχ1,
    Units.val_one, norm_one, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one]
  rw [Complex.ofReal_inv, Complex.ofReal_prod, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [shiftChar]
  simp only [Complex.finrank_real_complex]
  have hx : ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr (a i).ne_zero)
  rw [← Complex.cpow_neg_one, mul_assoc, mul_assoc, ← Complex.cpow_add _ _ hx,
    ← Complex.cpow_add _ _ hx]
  congr 2
  push_cast
  ring

theorem jacquetStep_mul (hh : h ∈ principalSeries ℂ (m + 1) χ) (hχ1 : χ m 1 = 1)
    (a : Fin m → ℂˣ) (u : upperUnipotent m ℂ) (g : Langlands.GeneralLinear m ℂ) :
    jacquetStep h ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear m ℂ) *
        (u : Langlands.GeneralLinear m ℂ) * g) =
      principalSeriesCharacter ℂ m (shiftChar χ) a * jacquetStep h g := by
  set b : Langlands.GeneralLinear m ℂ :=
    (Iwasawa.diagonalUnits a : Langlands.GeneralLinear m ℂ) * (u : Langlands.GeneralLinear m ℂ)
    with hbdef
  have hdet : ((b : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ).det =
      ∏ i, (a i : ℂ) := by
    rw [hbdef, Units.val_mul, Matrix.det_mul, det_upperUnipotent u, mul_one,
      Iwasawa.diagonalUnits_val, Matrix.det_diagonal]
  have hdet0 : ((b : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ).det ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (a i).ne_zero
  have hpt : ∀ x : Fin m → ℂ, h (chartGL x * iotaGL (b * g)) =
      principalSeriesCharacter ℂ (m + 1) χ (fun i => Fin.lastCases 1 a i) *
        h (chartGL (x ᵥ* ((b : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ)) *
          iotaGL g) := by
    intro x
    rw [map_mul, ← mul_assoc, chartGL_mul_iotaGL, mul_assoc]
    have hb : iotaGL b = (Iwasawa.diagonalUnits (fun i => Fin.lastCases 1 a i) :
        Langlands.GeneralLinear (m + 1) ℂ) *
        ((⟨iotaGL (u : Langlands.GeneralLinear m ℂ), iotaGL_mem_upperUnipotent u⟩ :
          upperUnipotent (m + 1) ℂ) : Langlands.GeneralLinear (m + 1) ℂ) := by
      rw [hbdef, map_mul, iotaGL_diagonalUnits]
    rw [hb]
    exact hh.2 _ _ _
  unfold jacquetStep
  rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul,
    integral_vecMul_eq hdet0 (fun y => h (chartGL y * iotaGL g)), ← mul_assoc, hdet,
    norm_prod, ← Finset.prod_pow, principalSeriesCharacter_lastCases hχ1]

/-! ## Finiteness under `U(m)` -/

theorem jacquetStep_rightTranslation (f : Langlands.GeneralLinear (m + 1) ℂ → ℂ)
    (g k : Langlands.GeneralLinear m ℂ) :
    jacquetStep (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (m + 1) ℂ) (iotaGL k) f) g =
      jacquetStep f (g * k) := by
  unfold jacquetStep
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  change f (chartGL x * iotaGL g * iotaGL k) = f (chartGL x * iotaGL (g * k))
  rw [map_mul, mul_assoc]

/-- The partial Jacquet integral restricted to `U(m)`, as a linear map on a submodule of the
principal series. -/
def jacquetStepOn (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e m)
    (V : Submodule ℂ (Langlands.GeneralLinear (m + 1) ℂ → ℂ))
    (hV : V ≤ principalSeries ℂ (m + 1) χ) :
    V →ₗ[ℂ] (Matrix.unitaryGroup (Fin m) ℂ → ℂ) where
  toFun f κ := jacquetStep (f : Langlands.GeneralLinear (m + 1) ℂ → ℂ) (Unitary.toUnits κ)
  map_add' f g := funext fun κ => by
    have hκ : iotaGL (Unitary.toUnits κ) ∈ unitaryCompact ℂ (m + 1) :=
      iotaGL_mem_unitaryCompact (k := Unitary.toUnits κ) κ.2
    simp only [jacquetStep, Submodule.coe_add, Pi.add_apply]
    exact integral_add (integrable_chart hχ he (hV f.2) hκ) (integrable_chart hχ he (hV g.2) hκ)
  map_smul' c f := funext fun κ => by
    simp only [jacquetStep, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

theorem finiteDimensional_jacquetStep (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e m)
    (hh : h ∈ kFiniteFunctions (principalSeries ℂ (m + 1) χ) (unitaryCompact ℂ (m + 1))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin m) ℂ =>
      fun x : Matrix.unitaryGroup (Fin m) ℂ => jacquetStep h (Unitary.toUnits (x * k)))) := by
  set V := Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ (m + 1) =>
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (m + 1) ℂ)
      (k : Langlands.GeneralLinear (m + 1) ℂ) h) with hVdef
  have hVfin : FiniteDimensional ℂ V := (mem_kFiniteVectors_iff _ _ _).mp hh.2
  have hV : V ≤ principalSeries ℂ (m + 1) χ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact rightTranslation_mem_principalSeries (χ := χ) hh.1 _
  have hle : Submodule.span ℂ (Set.range fun k : Matrix.unitaryGroup (Fin m) ℂ =>
      fun x : Matrix.unitaryGroup (Fin m) ℂ => jacquetStep h (Unitary.toUnits (x * k))) ≤
      LinearMap.range (jacquetStepOn hχ he V hV) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    have hk : iotaGL (Unitary.toUnits k) ∈ unitaryCompact ℂ (m + 1) :=
      iotaGL_mem_unitaryCompact (k := Unitary.toUnits k) k.2
    refine ⟨⟨_, Submodule.subset_span ⟨⟨_, hk⟩, rfl⟩⟩, funext fun x => ?_⟩
    change jacquetStep _ (Unitary.toUnits x) = jacquetStep h (Unitary.toUnits (x * k))
    rw [jacquetStep_rightTranslation, map_mul]
  exact Submodule.finiteDimensional_of_le hle

/-! ## The partial Jacquet integral lies in the shifted principal series -/

theorem phaseMatrix_toUnits (a : Fin m → ℂˣ) (κ : Matrix.unitaryGroup (Fin m) ℂ) :
    Unitary.toUnits (phaseMatrix a * κ) =
      (Iwasawa.diagonalUnits (fun i => phaseUnit (a i)) : Langlands.GeneralLinear m ℂ) *
        ((1 : upperUnipotent m ℂ) : Langlands.GeneralLinear m ℂ) * Unitary.toUnits κ := by
  apply Units.ext
  simp only [map_mul, Units.val_mul, OneMemClass.coe_one, mul_one, Iwasawa.diagonalUnits_val]
  rfl

/-- **The partial Jacquet integral.** For strictly dominant phase-power characters, the partial
Jacquet integral of a `U(m+1)`-finite function of the principal series of `χ` on `GL_{m+1}(ℂ)` is a
`U(m)`-finite function of the principal series of `χ |·|_ℂ^{-1/2}` on `GL_m(ℂ)`. -/
theorem jacquetStep_mem (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e m)
    (hh : h ∈ kFiniteFunctions (principalSeries ℂ (m + 1) χ) (unitaryCompact ℂ (m + 1))) :
    jacquetStep h ∈ kFiniteFunctions (principalSeries ℂ m (shiftChar χ)) (unitaryCompact ℂ m) := by
  set φ : Matrix.unitaryGroup (Fin m) ℂ → ℂ := fun κ => jacquetStep h (Unitary.toUnits κ)
    with hφdef
  have hφc : Continuous φ := continuous_jacquetStep_unitary hχ he hh.1
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin m) ℂ => fun x => φ (x * k))) :=
    finiteDimensional_jacquetStep hχ he hh
  have hφM : ∀ (a : Fin m → ℂˣ) (κ : Matrix.unitaryGroup (Fin m) ℂ),
      φ (phaseMatrix a * κ) =
        principalSeriesCharacter ℂ m (shiftChar χ) (fun i => phaseUnit (a i)) * φ κ := by
    intro a κ
    simp only [hφdef]
    rw [phaseMatrix_toUnits, jacquetStep_mul hh.1 (hχ.one m)]
  have hE := extension_mem_kFiniteFunctions (fun l => e l - 1 / 2) hχ.shift.eq hφc hfin hφM
  convert hE using 1
  funext g
  obtain ⟨a, u, k, hk, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  rw [jacquetStep_mul hh.1 (hχ.one m), hE.1.2 a u k]
  congr 1
  have hku : k = Unitary.toUnits (⟨(k : Matrix (Fin m) (Fin m) ℂ), hk⟩ :
      Matrix.unitaryGroup (Fin m) ℂ) := Units.ext rfl
  rw [hku, extension_unitary]

end ComplexPartialJacquet

/-- **The partial Jacquet integral of `GL_{m+1}(ℂ)` along `P_{m,1}`.** Let `χ_0, …, χ_m` be
characters of `ℂˣ` of the form `χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}` with `χ_l(1) = 1` and
`|χ_l| = 1` on the unit circle, and with `Re e_0 > Re e_1 > ⋯ > Re e_m`. For every
`U(m+1)`-finite function `h` of the smooth principal series of `χ` on `GL_{m+1}(ℂ)`, the function
`x ↦ h(J(x,1) κ)` on `ℂ^m` is integrable for every `κ ∈ U(m+1)`, and
`g ↦ ∫_{ℂ^m} h(J(x,1) diag(g,1)) dx` is a `U(m)`-finite function of the smooth principal series of
the characters `χ_l(z) (|z|²)^{-1/2}` on `GL_m(ℂ)`. Here `J(x,1)` is the identity matrix with last
row `(x, 1)`. -/
def ComplexPartialJacquetStatement : Prop :=
  ∀ (m : ℕ) (χ : ℕ → ℂˣ → ℂ) (e : ℕ → ℂ),
    (∀ (l : ℕ) (z : ℂˣ), χ l z =
      χ l (ComplexGramFormula.phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l) →
    (∀ l : ℕ, χ l 1 = 1) →
    (∀ (l : ℕ) (z : ℂˣ), ‖χ l (ComplexGramFormula.phaseUnit z)‖ = 1) →
    (∀ l : ℕ, l < m → (e (l + 1)).re < (e l).re) →
    ∀ h ∈ kFiniteFunctions (principalSeries ℂ (m + 1) χ) (unitaryCompact ℂ (m + 1)),
      (∀ κ ∈ unitaryCompact ℂ (m + 1), Integrable fun x : Fin m → ℂ =>
        h (ComplexMaximalParabolicIntegration.chartGL x * κ)) ∧
      (fun g : Langlands.GeneralLinear m ℂ => ∫ x : Fin m → ℂ,
          h (ComplexMaximalParabolicIntegration.chartGL x *
            ComplexMaximalParabolicIntegration.iotaGL g)) ∈
        kFiniteFunctions (principalSeries ℂ m
          (fun l z => χ l z * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))))
          (unitaryCompact ℂ m)

theorem complexPartialJacquet : ComplexPartialJacquetStatement := by
  intro m χ e heq hone hphase hdom h hh
  have hχ : ComplexPartialJacquet.IsPhasePower χ e := ⟨heq, hone, hphase⟩
  exact ⟨fun κ hκ => ComplexPartialJacquet.integrable_chart hχ hdom hh.1 hκ,
    ComplexPartialJacquet.jacquetStep_mem hχ hdom hh⟩

end Langlands.Archimedean
