import Langlands.Representation.Archimedean.ComplexDuality.UnitaryHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Integrals over `U(n)` of functions of the last row

For a bounded measurable function `Φ` on `ℂ^(m+1)` with `Φ(s x) = Φ(x)` for every complex
`s ≠ 0`, the integral of `Φ(last row of k)` over `U(m+1)` is a weighted Lebesgue integral over the
affine chart `v ↦ (v, 1)` of `ℂ^m`, with weight `(1 + |v|²)^(-(m+1))`
(`ComplexLastRowIntegral.integral_lastRow`). The proof averages a Gaussian on `ℂ^(m+1)` over
`U(m+1)` and computes it a second time in the chart.
-/

noncomputable section

open MeasureTheory Matrix

open scoped ComplexConjugate

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexLastRowIntegral

open ComplexDuality

variable {n : ℕ}

/-! ## Squared norms and unitary changes of variables -/

/-- The squared Hermitian norm `∑ |xᵢ|²`. -/
def sqNorm (x : Fin n → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

theorem sqNorm_nonneg (x : Fin n → ℂ) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sqNorm_smul (s : ℂ) (x : Fin n → ℂ) : sqNorm (s • x) = ‖s‖ ^ 2 * sqNorm x := by
  simp only [sqNorm, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

theorem ofReal_sqNorm (x : Fin n → ℂ) : ((sqNorm x : ℝ) : ℂ) = x ⬝ᵥ star x := by
  simp only [sqNorm, dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- Unitary matrices preserve the squared norm of row vectors. -/
theorem sqNorm_vecMul {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ * κᴴ = 1) (x : Fin n → ℂ) :
    sqNorm (x ᵥ* κ) = sqNorm x := by
  have h : ((sqNorm (x ᵥ* κ) : ℝ) : ℂ) = ((sqNorm x : ℝ) : ℂ) := by
    rw [ofReal_sqNorm, ofReal_sqNorm, star_vecMul, ← dotProduct_mulVec, mulVec_mulVec, hκ,
      one_mulVec]
  exact_mod_cast h

/-- A complex-linear change of variables on `ℂ^k` multiplies Lebesgue integrals by the inverse
of the squared modulus of its determinant. -/
theorem integral_comp_linearEquiv {k : ℕ} (L : (Fin k → ℂ) ≃ₗ[ℂ] (Fin k → ℂ))
    (g : (Fin k → ℂ) → ℂ) :
    ∫ x, g (L x) =
      ((Complex.normSq (LinearMap.det (L : (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ))))⁻¹ : ℝ) •
        ∫ x, g x := by
  set Lr : (Fin k → ℂ) ≃ₗ[ℝ] (Fin k → ℂ) := L.restrictScalars ℝ
  have hdet : LinearMap.det (Lr : (Fin k → ℂ) →ₗ[ℝ] (Fin k → ℂ)) =
      Complex.normSq (LinearMap.det (L : (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ))) := by
    have := LinearMap.det_restrictScalars (R := ℝ) (S := ℂ) (A := Fin k → ℂ)
      (f := (L : (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ)))
    rw [Algebra.norm_complex_apply] at this
    exact this
  have hunit : IsUnit (LinearMap.det (L : (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ))) :=
    LinearEquiv.isUnit_det' L
  have hne : Complex.normSq (LinearMap.det (L : (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ))) ≠ 0 :=
    (Complex.normSq_pos.mpr hunit.ne_zero).ne'
  have hpos : 0 < Complex.normSq (LinearMap.det (L : (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ))) :=
    Complex.normSq_pos.mpr hunit.ne_zero
  let e : (Fin k → ℂ) ≃ᵐ (Fin k → ℂ) :=
    (LinearEquiv.toContinuousLinearEquiv Lr).toHomeomorph.toMeasurableEquiv
  have hmap : Measure.map e volume = ENNReal.ofReal
      |(Complex.normSq (LinearMap.det (L : (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ))))⁻¹| •
        (volume : Measure (Fin k → ℂ)) := by
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar
      (μ := (volume : Measure (Fin k → ℂ)))
      (f := (Lr : (Fin k → ℂ) →ₗ[ℝ] (Fin k → ℂ))) (by rw [hdet]; exact hne)
    rw [hdet] at this
    exact this
  have h := integral_map_equiv (μ := (volume : Measure (Fin k → ℂ))) e g
  rw [hmap, integral_smul_measure, abs_inv, abs_of_pos hpos,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hpos.le)] at h
  exact h.symm

/-- Right multiplication by a unitary matrix preserves Lebesgue measure on row vectors. -/
theorem integral_vecMul {κ : Matrix (Fin n) (Fin n) ℂ} (hκ : κ * κᴴ = 1)
    (g : (Fin n → ℂ) → ℂ) : ∫ x, g (x ᵥ* κ) = ∫ x, g x := by
  have hκ' : κᴴ * κ = 1 := mul_eq_one_comm.mp hκ
  let L : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x => x ᵥ* κ
      invFun := fun x => x ᵥ* κᴴ
      map_add' := fun x y => add_vecMul κ x y
      map_smul' := fun c x => by simp [smul_vecMul]
      left_inv := fun x => by simp [vecMul_vecMul, hκ]
      right_inv := fun x => by simp [vecMul_vecMul, hκ'] }
  have hdet : LinearMap.det (L : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = κ.det := by
    have : (L : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = Matrix.toLin' κᵀ := by
      apply LinearMap.ext
      intro x
      simp [L, Matrix.toLin'_apply, mulVec_transpose]
    rw [this, LinearMap.det_toLin', det_transpose]
  have hdet1 : Complex.normSq κ.det = 1 := by
    have h1 := congrArg Matrix.det hκ
    rw [det_mul, det_conjTranspose, det_one] at h1
    have : (Complex.normSq κ.det : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self, mul_comm]
      exact h1
    exact_mod_cast this
  have h := integral_comp_linearEquiv L g
  rw [hdet, hdet1, inv_one, one_smul] at h
  exact h

/-! ## Householder reflections -/

theorem sqNorm_eq_one_lastRow_phase {m : ℕ} (u : Fin (m + 1) → ℂ) :
    ∃ θ : ℂ, ‖θ‖ = 1 ∧ (conj θ * u (Fin.last m)).im = 0 ∧ 0 ≤ (conj θ * u (Fin.last m)).re := by
  by_cases hu : u (Fin.last m) = 0
  · exact ⟨1, by simp, by simp [hu], by simp [hu]⟩
  · refine ⟨u (Fin.last m) / (‖u (Fin.last m)‖ : ℂ), ?_, ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hu)]
    · have : conj (u (Fin.last m) / (‖u (Fin.last m)‖ : ℂ)) * u (Fin.last m) =
          ((‖u (Fin.last m)‖ : ℝ) : ℂ) := by
        rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm,
          Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have hn : (‖u (Fin.last m)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hu
        field_simp
        push_cast
        ring
      rw [this, Complex.ofReal_im]
    · have : conj (u (Fin.last m) / (‖u (Fin.last m)‖ : ℂ)) * u (Fin.last m) =
          ((‖u (Fin.last m)‖ : ℝ) : ℂ) := by
        rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm,
          Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have hn : (‖u (Fin.last m)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hu
        field_simp
        push_cast
        ring
      rw [this, Complex.ofReal_re]
      exact norm_nonneg _

/-- **Householder reflection.** Every unit row vector with real nonnegative last entry is the last
row of a unitary matrix. -/
theorem exists_unitary_lastRow_of_real {m : ℕ} (u : Fin (m + 1) → ℂ) (hu : sqNorm u = 1)
    (him : (u (Fin.last m)).im = 0) :
    ∃ κ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, κ * κᴴ = 1 ∧ κ (Fin.last m) = u := by
  classical
  set e : Fin (m + 1) → ℂ := Pi.single (Fin.last m) 1 with he
  by_cases hue : u = e
  · refine ⟨1, by simp, ?_⟩
    rw [hue]
    funext j
    simp only [he, Matrix.one_apply, Pi.single_apply]
    by_cases h : j = Fin.last m
    · simp [h]
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
  set w := e - u with hw
  set ul := u (Fin.last m) with hul
  have hulr : ul = ((ul.re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
  have huu : u ⬝ᵥ star u = 1 := by rw [← ofReal_sqNorm, hu, Complex.ofReal_one]
  have hstar_ul : star ul = ul := by
    rw [hulr, Complex.star_def, Complex.conj_ofReal]
  have hse : star e = e := by
    funext j
    simp only [he, Pi.star_apply, Pi.single_apply]
    split_ifs <;> simp
  have hc_eq : w ⬝ᵥ star w = 2 * (1 - ul) := by
    rw [hw, star_sub, hse, sub_dotProduct, dotProduct_sub, dotProduct_sub, huu, he]
    simp only [single_dotProduct, dotProduct_single, Pi.star_apply, Pi.single_eq_same,
      one_mul, mul_one]
    rw [← hul, hstar_ul]
    ring
  have hlast : ul ≠ 1 := by
    intro h1
    apply hue
    have hsum : ∑ i, ‖u i‖ ^ 2 = 1 := hu
    rw [Fin.sum_univ_castSucc, ← hul, h1, norm_one, one_pow, add_eq_right] at hsum
    have hzero : ∀ i : Fin m, u i.castSucc = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖u (Fin.castSucc j)‖)).mp
        hsum i (Finset.mem_univ i)
      exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [he, ← hul, h1]
    · rw [hzero i, he, Pi.single_apply, ite_eq_right (Fin.castSucc_lt_last i).ne]
  have hc : w ⬝ᵥ star w ≠ 0 := by
    rw [hc_eq]
    exact mul_ne_zero two_ne_zero (sub_ne_zero.mpr (Ne.symm hlast))
  set a : ℂ := 2 / (w ⬝ᵥ star w) with ha
  set H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := 1 - a • vecMulVec (star w) w with hH
  have hastar : star a = a := by
    rw [ha, hc_eq, star_div₀, star_mul', star_sub, star_one, hstar_ul]
    simp
  refine ⟨H, ?_, ?_⟩
  · have hT : Hᴴ = H := by
      rw [hH, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hastar]
      congr 2
      ext i j
      simp [vecMulVec_apply, mul_comm]
    have hVV : vecMulVec (star w) w * vecMulVec (star w) w =
        (w ⬝ᵥ star w) • vecMulVec (star w) w := by
      rw [vecMulVec_mul_vecMulVec]
      ext i j
      simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
      rw [dotProduct_comm]
      ring
    have hcoef : a * a * (w ⬝ᵥ star w) = 2 * a := by
      rw [ha]
      field_simp
    rw [hT, hH]
    calc (1 - a • vecMulVec (star w) w) * (1 - a • vecMulVec (star w) w)
        = 1 - (2 * a - a * a * (w ⬝ᵥ star w)) • vecMulVec (star w) w := by
          rw [sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
            Matrix.smul_mul, Matrix.mul_smul, hVV, smul_smul, smul_smul]
          module
      _ = 1 := by rw [hcoef, sub_self, zero_smul, sub_zero]
  · funext j
    have hk : a * star (w (Fin.last m)) = 1 := by
      have hwl : w (Fin.last m) = 1 - ul := by
        rw [hw, Pi.sub_apply, he, Pi.single_eq_same]
      rw [hwl, star_sub, star_one, hstar_ul, ha, hc_eq]
      have : (1 : ℂ) - ul ≠ 0 := sub_ne_zero.mpr (Ne.symm hlast)
      field_simp
    simp only [hH, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
      Pi.star_apply]
    rw [← mul_assoc, hk, one_mul, hw, Pi.sub_apply, Matrix.one_apply, he, Pi.single_apply]
    by_cases h : j = Fin.last m
    · subst h
      simp
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
      ring

/-- Every unit row vector is the last row of a unitary matrix. -/
theorem exists_unitary_lastRow {m : ℕ} (u : Fin (m + 1) → ℂ) (hu : sqNorm u = 1) :
    ∃ κ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, κ * κᴴ = 1 ∧ κ (Fin.last m) = u := by
  obtain ⟨θ, hθ, him, -⟩ := sqNorm_eq_one_lastRow_phase u
  have hθu : sqNorm (conj θ • u) = 1 := by
    rw [sqNorm_smul, Complex.norm_conj, hθ, one_pow, one_mul, hu]
  obtain ⟨κ₀, hκ₀, hlast⟩ := exists_unitary_lastRow_of_real (conj θ • u) hθu
    (by simpa using him)
  set D : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    Matrix.diagonal (Function.update (fun _ => (1 : ℂ)) (Fin.last m) θ) with hD
  have hDD : D * Dᴴ = 1 := by
    rw [hD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases hi : i = Fin.last m
    · subst hi
      simp only [Pi.star_apply, Function.update_self]
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hθ]
      simp
    · simp [Function.update_of_ne hi]
  refine ⟨D * κ₀, ?_, ?_⟩
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κ₀, hκ₀, Matrix.one_mul, hDD]
  · funext j
    rw [hD, Matrix.diagonal_mul, Function.update_self, hlast, Pi.smul_apply, smul_eq_mul,
      ← mul_assoc]
    have : θ * conj θ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hθ]
      simp
    rw [this, one_mul]

/-! ## Averaging over `U(n)` -/

/-- The Gaussian weight `exp(-∑ |xᵢ|²)`. -/
def gaussian (x : Fin n → ℂ) : ℝ := Real.exp (-sqNorm x)

theorem integrable_exp_neg_norm_sq_complex : Integrable fun z : ℂ => Real.exp (-‖z‖ ^ 2) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := 1) (by simp) 0 0
  refine h.norm.congr (ae_of_all _ fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  simp [← Complex.ofReal_pow, Complex.neg_re]

theorem gaussian_eq_prod (x : Fin n → ℂ) : gaussian x = ∏ i, Real.exp (-‖x i‖ ^ 2) := by
  rw [gaussian, sqNorm, ← Real.exp_sum]
  congr 1
  simp [Finset.sum_neg_distrib]

theorem integrable_gaussian : Integrable (gaussian (n := n)) := by
  have h := Integrable.fintype_prod (𝕜 := ℝ) (ι := Fin n)
    (f := fun _ z => Real.exp (-‖z‖ ^ 2)) (μ := fun _ => (volume : Measure ℂ))
    (fun _ => integrable_exp_neg_norm_sq_complex)
  have : gaussian (n := n) = fun x : Fin n → ℂ => ∏ i, Real.exp (-‖x i‖ ^ 2) :=
    funext gaussian_eq_prod
  rw [this]
  exact h

/-- The last row of a unitary matrix. -/
def lastRow {m : ℕ} (k : unitaryCompact ℂ (m + 1)) : Fin (m + 1) → ℂ :=
  ((k : Langlands.GeneralLinear (m + 1) ℂ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m)

theorem mul_conjTranspose_eq_one {m : ℕ} (k : unitaryCompact ℂ m) :
    ((k : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) *
      ((k : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ)ᴴ = 1 := by
  have := Matrix.mem_unitaryGroup_iff.mp k.2
  rwa [Matrix.star_eq_conjTranspose] at this

theorem lastRow_mul {m : ℕ} (k₀ k : unitaryCompact ℂ (m + 1)) :
    lastRow (k₀ * k) = lastRow k₀ ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℂ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
  funext j
  simp only [lastRow, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, vecMul, dotProduct]

/-- A function of degree-zero homogeneity: `Φ(s x) = Φ(x)` for complex `s ≠ 0`. -/
def IsHomogeneousZero {m : ℕ} (Φ : (Fin m → ℂ) → ℂ) : Prop :=
  ∀ (s : ℂ), s ≠ 0 → ∀ x, Φ (s • x) = Φ x

/-- For a homogeneous `Φ` and a nonzero row vector `x`, `∫_{U(n)} Φ(x k) dk` is the integral of
`Φ` over the last rows. -/
theorem integral_vecMul_eq {m : ℕ} {Φ : (Fin (m + 1) → ℂ) → ℂ} (hΦ : IsHomogeneousZero Φ)
    {x : Fin (m + 1) → ℂ} (hx : x ≠ 0) :
    ∫ k, Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℂ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) ∂unitaryHaar (m + 1) =
      ∫ k, Φ (lastRow k) ∂unitaryHaar (m + 1) := by
  have hpos : 0 < sqNorm x := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext h)
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i))
  set r := Real.sqrt (sqNorm x) with hr
  have hr0 : r ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  set u := ((r⁻¹ : ℝ) : ℂ) • x with hu
  have hu1 : sqNorm u = 1 := by
    rw [hu, sqNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, inv_pow, sq_abs,
      hr, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  obtain ⟨κ₀, hκ₀, hlast⟩ := exists_unitary_lastRow u hu1
  have hκ₀mem : κ₀ ∈ Matrix.unitaryGroup (Fin (m + 1)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    exact hκ₀
  let k₀ : unitaryCompact ℂ (m + 1) := ⟨Unitary.toUnits ⟨κ₀, hκ₀mem⟩, hκ₀mem⟩
  have hxu : x = (r : ℂ) • lastRow k₀ := by
    have : lastRow k₀ = u := hlast
    rw [this, hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr0, Complex.ofReal_one,
      one_smul]
  have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
  calc ∫ k, Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℂ) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) ∂unitaryHaar (m + 1)
      = ∫ k, Φ (lastRow (k₀ * k)) ∂unitaryHaar (m + 1) := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        simp only
        rw [hxu, smul_vecMul, hΦ (r : ℂ) hr0', lastRow_mul]
    _ = ∫ k, Φ (lastRow k) ∂unitaryHaar (m + 1) :=
        integral_mul_left_eq_self (μ := unitaryHaar (m + 1)) (fun k => Φ (lastRow k)) k₀

theorem continuous_unitaryCompact_val {m : ℕ} :
    Continuous fun k : unitaryCompact ℂ m =>
      ((k : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) :=
  Units.continuous_val.comp continuous_subtype_val

theorem measurable_vecMul_unitary {m : ℕ} :
    Measurable fun p : unitaryCompact ℂ m × (Fin m → ℂ) =>
      p.2 ᵥ* ((p.1 : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) := by
  have hc : Continuous fun p : unitaryCompact ℂ m × (Fin m → ℂ) =>
      p.2 ᵥ* ((p.1 : Langlands.GeneralLinear m ℂ) : Matrix (Fin m) (Fin m) ℂ) := by
    refine continuous_pi fun j => ?_
    simp only [vecMul, dotProduct]
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((continuous_apply i).comp continuous_snd).mul
      ((continuous_apply j).comp ((continuous_apply i).comp
        (continuous_unitaryCompact_val.comp continuous_fst)))
  exact hc.measurable

/-- **Averaging.** For a bounded measurable homogeneous `Φ`,
`∫ Φ(x) e^{-|x|²} dx = (∫_{U(n)} Φ(last row of k) dk) · ∫ e^{-|x|²} dx`. -/
theorem integral_mul_gaussian_eq {m : ℕ} {Φ : (Fin (m + 1) → ℂ) → ℂ} (hmeas : Measurable Φ)
    {C : ℝ} (hC : ∀ x, ‖Φ x‖ ≤ C) (hΦ : IsHomogeneousZero Φ) :
    ∫ x, Φ x * (gaussian x : ℂ) =
      (∫ k, Φ (lastRow k) ∂unitaryHaar (m + 1)) * ∫ x : Fin (m + 1) → ℂ, (gaussian x : ℂ) := by
  set J := ∫ k, Φ (lastRow k) ∂unitaryHaar (m + 1)
  have hrot : ∀ k : unitaryCompact ℂ (m + 1), ∫ x, Φ x * (gaussian x : ℂ) =
      ∫ x, Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℂ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) * (gaussian x : ℂ) := by
    intro k
    rw [← integral_vecMul (mul_conjTranspose_eq_one k) (fun x => Φ x * (gaussian x : ℂ))]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [gaussian, sqNorm_vecMul (mul_conjTranspose_eq_one k)]
  have hint : Integrable (Function.uncurry fun (k : unitaryCompact ℂ (m + 1))
      (x : Fin (m + 1) → ℂ) => Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℂ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) * (gaussian x : ℂ))
      ((unitaryHaar (m + 1)).prod volume) := by
    have hb : Integrable (fun z : unitaryCompact ℂ (m + 1) × (Fin (m + 1) → ℂ) =>
        C * gaussian z.2) ((unitaryHaar (m + 1)).prod volume) :=
      (integrable_const C).mul_prod integrable_gaussian
    refine hb.mono' ?_ (ae_of_all _ fun z => ?_)
    · have : Measurable (Function.uncurry fun (k : unitaryCompact ℂ (m + 1))
          (x : Fin (m + 1) → ℂ) => Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℂ) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) * (gaussian x : ℂ)) := by
        refine (hmeas.comp measurable_vecMul_unitary).mul ?_
        refine Complex.measurable_ofReal.comp ?_
        have hc : Continuous (gaussian (n := m + 1)) := by
          unfold gaussian sqNorm
          fun_prop
        exact hc.measurable.comp measurable_snd
      exact this.aestronglyMeasurable
    · obtain ⟨k, x⟩ := z
      show ‖Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℂ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) * ((gaussian x : ℝ) : ℂ)‖ ≤ C * gaussian x
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (show 0 ≤ gaussian x from (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_right (hC _) (Real.exp_pos _).le
  calc ∫ x, Φ x * (gaussian x : ℂ)
      = ∫ k : unitaryCompact ℂ (m + 1), (∫ x, Φ x * (gaussian x : ℂ)) ∂unitaryHaar (m + 1) := by
        rw [integral_const, probReal_univ, one_smul]
    _ = ∫ k : unitaryCompact ℂ (m + 1), (∫ x, Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℂ) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) * (gaussian x : ℂ)) ∂unitaryHaar (m + 1) :=
        integral_congr_ae (ae_of_all _ hrot)
    _ = ∫ x, ∫ k, Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℂ) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) * (gaussian x : ℂ) ∂unitaryHaar (m + 1) :=
        integral_integral_swap hint
    _ = ∫ x, J * (gaussian x : ℂ) := by
        have hnull : ∀ᵐ x : Fin (m + 1) → ℂ, x ≠ 0 := by
          rw [ae_iff]
          simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
          exact measure_singleton 0
        refine integral_congr_ae (hnull.mono fun x hx => ?_)
        simp only
        rw [integral_mul_const, integral_vecMul_eq hΦ hx]
    _ = J * ∫ x, (gaussian x : ℂ) := integral_const_mul J _


/-! ## The affine chart of the last coordinate -/

theorem integrable_exp_neg_mul_norm_sq_complex {c : ℝ} (hc : 0 < c) :
    Integrable fun z : ℂ => Real.exp (-(c * ‖z‖ ^ 2)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (c : ℂ))
    (by simpa using hc) 0 0
  refine h.norm.congr (ae_of_all _ fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  simp [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.neg_re]

/-- The complex Gaussian moment `∫_ℂ |t|^(2m) e^{-|t|²} dt`. -/
def gaussianMoment (m : ℕ) : ℝ := ∫ t : ℂ, ‖t‖ ^ (2 * m) * Real.exp (-‖t‖ ^ 2)

theorem integrable_norm_pow_mul_exp (m : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable fun t : ℂ => ‖t‖ ^ (2 * m) * Real.exp (-(a * ‖t‖ ^ 2)) := by
  have hb := (integrable_exp_neg_mul_norm_sq_complex (half_pos ha)).const_mul
    ((m.factorial : ℝ) * (2 / a) ^ m)
  refine hb.mono' ?_ (ae_of_all _ fun t => ?_)
  · have hc : Continuous fun t : ℂ => ‖t‖ ^ (2 * m) * Real.exp (-(a * ‖t‖ ^ 2)) := by
      fun_prop
    exact hc.aestronglyMeasurable
  · have hx : 0 ≤ a / 2 * ‖t‖ ^ 2 := by positivity
    have hfact := Real.pow_div_factorial_le_exp _ hx m
    have hfpos : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    rw [div_le_iff₀ hfpos] at hfact
    have hkey : ‖t‖ ^ (2 * m) ≤ (m.factorial : ℝ) * (2 / a) ^ m * Real.exp (a / 2 * ‖t‖ ^ 2) := by
      have h2 : ‖t‖ ^ (2 * m) = (2 / a) ^ m * (a / 2 * ‖t‖ ^ 2) ^ m := by
        have h22 : (2 / a) * (a / 2) = 1 := by field_simp
        rw [mul_pow, ← mul_assoc, ← mul_pow, h22, one_pow, one_mul, ← pow_mul]
      rw [h2]
      have h3 : (a / 2 * ‖t‖ ^ 2) ^ m ≤ Real.exp (a / 2 * ‖t‖ ^ 2) * m.factorial := hfact
      have h4 : (0 : ℝ) ≤ (2 / a) ^ m := by positivity
      calc (2 / a) ^ m * (a / 2 * ‖t‖ ^ 2) ^ m
          ≤ (2 / a) ^ m * (Real.exp (a / 2 * ‖t‖ ^ 2) * m.factorial) :=
            mul_le_mul_of_nonneg_left h3 h4
        _ = (m.factorial : ℝ) * (2 / a) ^ m * Real.exp (a / 2 * ‖t‖ ^ 2) := by ring
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖t‖ ^ (2 * m) * Real.exp (-(a * ‖t‖ ^ 2))
        ≤ ((m.factorial : ℝ) * (2 / a) ^ m * Real.exp (a / 2 * ‖t‖ ^ 2)) *
            Real.exp (-(a * ‖t‖ ^ 2)) :=
          mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
      _ = (m.factorial : ℝ) * (2 / a) ^ m * Real.exp (-(a / 2 * ‖t‖ ^ 2)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

theorem integral_norm_pow_mul_exp_scale (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ t : ℂ, ‖t‖ ^ (2 * m) * Real.exp (-(a * ‖t‖ ^ 2)) = (a ^ (m + 1))⁻¹ * gaussianMoment m := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have h := Measure.integral_comp_smul (μ := (volume : Measure ℂ))
    (fun t : ℂ => ‖t‖ ^ (2 * m) * Real.exp (-‖t‖ ^ 2)) (Real.sqrt a)
  have hpt : ∀ x : ℂ, ‖Real.sqrt a • x‖ ^ (2 * m) * Real.exp (-‖Real.sqrt a • x‖ ^ 2) =
      a ^ m * (‖x‖ ^ (2 * m) * Real.exp (-(a * ‖x‖ ^ 2))) := fun x => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow, mul_pow, pow_mul,
      Real.sq_sqrt ha.le, pow_mul]
    ring
  simp only [hpt] at h
  rw [integral_const_mul, Complex.finrank_real_complex, Real.sq_sqrt ha.le, abs_inv,
    abs_of_pos ha, smul_eq_mul] at h
  have hne : a ^ m ≠ 0 := pow_ne_zero _ ha.ne'
  rw [gaussianMoment, pow_succ, mul_inv, mul_assoc, ← h]
  field_simp

theorem snoc_smul_one {m : ℕ} (s : ℂ) (v : Fin m → ℂ) :
    (Fin.snoc (s • v) s : Fin (m + 1) → ℂ) = s • (Fin.snoc v 1 : Fin (m + 1) → ℂ) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · simp

theorem sqNorm_snoc {m : ℕ} (v : Fin m → ℂ) (s : ℂ) :
    sqNorm (Fin.snoc v s : Fin (m + 1) → ℂ) = sqNorm v + ‖s‖ ^ 2 := by
  simp [sqNorm, Fin.sum_univ_castSucc]

/-- The chart weight `(1 + |v|²)^{-(m+1)}`. -/
def chartWeight {m : ℕ} (v : Fin m → ℂ) : ℝ := ((1 + sqNorm v) ^ (m + 1))⁻¹

theorem norm_sq_le_sqNorm {m : ℕ} (v : Fin m → ℂ) : ‖v‖ ^ 2 ≤ sqNorm v := by
  have h : ‖v‖ ≤ Real.sqrt (sqNorm v) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    exact Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun j => ‖v j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  calc ‖v‖ ^ 2 ≤ Real.sqrt (sqNorm v) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = sqNorm v := Real.sq_sqrt (sqNorm_nonneg v)

theorem chartWeight_nonneg {m : ℕ} (v : Fin m → ℂ) : 0 ≤ chartWeight v :=
  inv_nonneg.mpr (pow_nonneg (by linarith [sqNorm_nonneg v]) _)

theorem continuous_sqNorm {m : ℕ} : Continuous (sqNorm (n := m)) := by
  unfold sqNorm
  fun_prop

theorem integrable_chartWeight {m : ℕ} : Integrable (chartWeight (m := m)) := by
  have hfin : Module.finrank ℝ (Fin m → ℂ) = 2 * m := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Complex.finrank_real_complex, smul_eq_mul, mul_comm]
  have h := integrable_rpow_neg_one_add_norm_sq (E := Fin m → ℂ) (μ := volume)
    (r := 2 * ((m : ℝ) + 1)) (by rw [hfin]; push_cast; linarith)
  refine h.mono' ?_ (ae_of_all _ fun v => ?_)
  · have hc : Continuous (chartWeight (m := m)) := by
      unfold chartWeight
      refine Continuous.inv₀ ((continuous_const.add continuous_sqNorm).pow _) fun v => ?_
      exact pow_ne_zero _ (by linarith [sqNorm_nonneg v])
    exact hc.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (chartWeight_nonneg v), chartWeight]
    have h1 : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by positivity
    have h2 : 1 + ‖v‖ ^ 2 ≤ 1 + sqNorm v := by linarith [norm_sq_le_sqNorm v]
    have h3 : (0 : ℝ) < 1 + sqNorm v := by linarith [sqNorm_nonneg v]
    rw [← Real.rpow_natCast, ← Real.rpow_neg h3.le]
    have : -(2 * ((m : ℝ) + 1)) / 2 = -(((m + 1 : ℕ) : ℝ)) := by push_cast; ring
    rw [this]
    exact Real.rpow_le_rpow_of_nonpos h1 h2 (by
      have := (Nat.cast_nonneg (m + 1) : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ))
      linarith)

theorem measurable_snoc {m : ℕ} :
    Measurable fun p : ℂ × (Fin m → ℂ) => (Fin.snoc p.2 p.1 : Fin (m + 1) → ℂ) := by
  refine measurable_pi_iff.mpr fun j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have : (fun p : ℂ × (Fin m → ℂ) => (Fin.snoc p.2 p.1 : Fin (m + 1) → ℂ) (Fin.last m)) =
        fun p => p.1 := funext fun p => by simp
    rw [this]
    exact measurable_fst
  · have : (fun p : ℂ × (Fin m → ℂ) => (Fin.snoc p.2 p.1 : Fin (m + 1) → ℂ) i.castSucc) =
        fun p => p.2 i := funext fun p => by simp
    rw [this]
    exact (measurable_pi_apply i).comp measurable_snd

/-- Complex scaling of `ℂ^m` multiplies Lebesgue measure by `|s|^(2m)`. -/
theorem integral_comp_complex_smul {m : ℕ} (g : (Fin m → ℂ) → ℂ) {s : ℂ} (hs : s ≠ 0) :
    ∫ v, g (s • v) = ((‖s‖ ^ (2 * m))⁻¹ : ℝ) • ∫ v, g v := by
  let L : (Fin m → ℂ) ≃ₗ[ℂ] (Fin m → ℂ) := LinearEquiv.smulOfNeZero ℂ (Fin m → ℂ) s hs
  have hdet : LinearMap.det (L : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) = s ^ m := by
    have : (L : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) = s • LinearMap.id := by
      apply LinearMap.ext
      intro v
      rfl
    rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_fin_fun]
  have h := integral_comp_linearEquiv L g
  rw [hdet, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul, mul_comm m 2] at h
  exact h

/-- **Chart.** For a bounded measurable homogeneous `Φ`,
`∫ Φ(x) e^{-|x|²} dx = (∫ |t|^(2m) e^{-|t|²} dt) · ∫ Φ(v, 1) (1 + |v|²)^{-(m+1)} dv`. -/
theorem integral_mul_gaussian_chart {m : ℕ} {Φ : (Fin (m + 1) → ℂ) → ℂ} (hmeas : Measurable Φ)
    {C : ℝ} (hC : ∀ x, ‖Φ x‖ ≤ C) (hΦ : IsHomogeneousZero Φ) :
    ∫ x, Φ x * (gaussian x : ℂ) =
      (gaussianMoment m : ℂ) * ∫ v : Fin m → ℂ, Φ (Fin.snoc v 1) * (chartWeight v : ℂ) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) (Fin.last m) with he
  have hp : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) (Fin.last m)
  set G : ℂ × (Fin m → ℂ) → ℂ := fun p =>
    Φ (Fin.snoc p.2 p.1) * (gaussian (Fin.snoc p.2 p.1 : Fin (m + 1) → ℂ) : ℂ) with hG
  have hsnoc : ∀ x : Fin (m + 1) → ℂ, (Fin.snoc (e x).2 (e x).1 : Fin (m + 1) → ℂ) = x := by
    intro x
    have h1 : (e x).1 = x (Fin.last m) := rfl
    have h2 : (e x).2 = Fin.init x := by
      funext j
      change x ((Fin.last m).succAbove j) = x j.castSucc
      rw [Fin.succAbove_last]
    rw [h1, h2, Fin.snoc_init_self]
  have hFG : (fun x => Φ x * (gaussian x : ℂ)) = G ∘ e := by
    funext x
    simp only [hG, Function.comp_apply, hsnoc]
  have hintF : Integrable (fun x : Fin (m + 1) → ℂ => Φ x * (gaussian x : ℂ)) := by
    refine (integrable_gaussian.ofReal (𝕜 := ℂ)).bdd_mul hmeas.aestronglyMeasurable
      (ae_of_all _ hC) |>.congr (ae_of_all _ fun x => ?_)
    simp
  have hintG : Integrable G (volume.prod volume) := by
    rw [← hp.integrable_comp_emb e.measurableEmbedding, ← hFG]
    exact hintF
  -- the inner integral over `y`
  have hinner : ∀ s : ℂ, s ≠ 0 → ∫ y, G (s, y) =
      ((‖s‖ ^ (2 * m) : ℝ) : ℂ) * ∫ v : Fin m → ℂ, Φ (Fin.snoc v 1) *
        ((Real.exp (-((1 + sqNorm v) * ‖s‖ ^ 2))) : ℂ) := by
    intro s hs
    have hsc := integral_comp_complex_smul (fun y => G (s, y)) hs
    have hval : ∀ v : Fin m → ℂ, G (s, s • v) = Φ (Fin.snoc v 1) *
        ((Real.exp (-((1 + sqNorm v) * ‖s‖ ^ 2))) : ℂ) := by
      intro v
      simp only [hG, snoc_smul_one, hΦ s hs, gaussian, sqNorm_smul, sqNorm_snoc]
      congr 3
      simp [sqNorm]
      ring
    simp only [hval] at hsc
    have hk : (‖s‖ ^ (2 * m) : ℝ) * (‖s‖ ^ (2 * m))⁻¹ = 1 :=
      mul_inv_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr hs))
    rw [hsc, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hk, Complex.ofReal_one,
      one_mul]
  -- the integrand after the inner substitution
  set H : ℂ × (Fin m → ℂ) → ℂ := fun p => Φ (Fin.snoc p.2 1) *
    ((‖p.1‖ ^ (2 * m) * Real.exp (-((1 + sqNorm p.2) * ‖p.1‖ ^ 2)) : ℝ) : ℂ) with hH
  have hHmeas : Measurable H := by
    refine (hmeas.comp (measurable_snoc.comp (measurable_const.prodMk measurable_snd))).mul ?_
    refine Complex.measurable_ofReal.comp ?_
    have hc : Continuous fun p : ℂ × (Fin m → ℂ) =>
        ‖p.1‖ ^ (2 * m) * Real.exp (-((1 + sqNorm p.2) * ‖p.1‖ ^ 2)) := by
      have := continuous_sqNorm (m := m)
      fun_prop
    exact hc.measurable
  have hintH : Integrable H (volume.prod volume) := by
    rw [integrable_prod_iff' hHmeas.aestronglyMeasurable]
    have hs_int : ∀ v : Fin m → ℂ, Integrable fun s : ℂ =>
        ‖s‖ ^ (2 * m) * Real.exp (-((1 + sqNorm v) * ‖s‖ ^ 2)) := fun v =>
      integrable_norm_pow_mul_exp m (by linarith [sqNorm_nonneg v])
    refine ⟨ae_of_all _ fun v => ?_, ?_⟩
    · show Integrable (fun s : ℂ => Φ (Fin.snoc v 1) *
        ((‖s‖ ^ (2 * m) * Real.exp (-((1 + sqNorm v) * ‖s‖ ^ 2)) : ℝ) : ℂ))
      exact ((hs_int v).ofReal (𝕜 := ℂ)).const_mul _
    have heq : (fun v : Fin m → ℂ => ∫ s, ‖H (s, v)‖) =
        fun v => ‖Φ (Fin.snoc v 1)‖ * (chartWeight v * gaussianMoment m) := by
      funext v
      have hn : ∀ s : ℂ, ‖H (s, v)‖ = ‖Φ (Fin.snoc v 1)‖ *
          (‖s‖ ^ (2 * m) * Real.exp (-((1 + sqNorm v) * ‖s‖ ^ 2))) := fun s => by
        show ‖Φ (Fin.snoc v 1) * ((‖s‖ ^ (2 * m) * Real.exp (-((1 + sqNorm v) * ‖s‖ ^ 2)) : ℝ) :
          ℂ)‖ = _
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
          (mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le)]
      rw [integral_congr_ae (ae_of_all _ hn), integral_const_mul,
        integral_norm_pow_mul_exp_scale m (by linarith [sqNorm_nonneg v]), chartWeight]
    rw [heq]
    refine ((integrable_chartWeight.mul_const (gaussianMoment m)).bdd_mul (c := C)
      ((hmeas.comp (measurable_snoc.comp (measurable_const.prodMk measurable_id))).norm.aestronglyMeasurable)
      (ae_of_all _ fun v => ?_))
    rw [norm_norm]
    exact hC _
  calc ∫ x, Φ x * (gaussian x : ℂ)
      = ∫ p, G p ∂(volume.prod volume) := by
        rw [hFG]
        exact hp.integral_comp' (f := e) G
    _ = ∫ s, ∫ y, G (s, y) := integral_prod G hintG
    _ = ∫ s, ∫ v, H (s, v) := by
        have hnull : ∀ᵐ s : ℂ, s ≠ 0 := by
          rw [ae_iff]
          simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
          exact measure_singleton 0
        refine integral_congr_ae (hnull.mono fun s hs => ?_)
        simp only
        rw [hinner s hs, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun v => ?_)
        simp only [hH]
        push_cast
        ring
    _ = ∫ v, ∫ s, H (s, v) := integral_integral_swap (f := fun s v => H (s, v)) hintH
    _ = ∫ v : Fin m → ℂ, (gaussianMoment m : ℂ) * (Φ (Fin.snoc v 1) * (chartWeight v : ℂ)) := by
        refine integral_congr_ae (ae_of_all _ fun v => ?_)
        simp only [hH]
        rw [integral_const_mul, integral_complex_ofReal,
          integral_norm_pow_mul_exp_scale m (by linarith [sqNorm_nonneg v]), chartWeight]
        push_cast
        ring
    _ = (gaussianMoment m : ℂ) * ∫ v : Fin m → ℂ, Φ (Fin.snoc v 1) * (chartWeight v : ℂ) :=
        integral_const_mul _ _

theorem integral_gaussian_pos {m : ℕ} : 0 < ∫ x : Fin m → ℂ, gaussian x := by
  have hpos : ∀ x : Fin m → ℂ, 0 < gaussian x := fun x => Real.exp_pos _
  rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) integrable_gaussian]
  have : Function.support (gaussian (n := m)) = Set.univ :=
    Set.eq_univ_of_forall fun x => (hpos x).ne'
  rw [this, Measure.measure_univ_pos]
  exact NeZero.ne _

/-- **Last-row formula.** For a bounded measurable `Φ` on `ℂ^(m+1)` with `Φ(s x) = Φ(x)` for
complex `s ≠ 0`, `∫_{U(m+1)} Φ(last row of k) dk = c_m ∫_{ℂ^m} Φ(v, 1) (1 + |v|²)^{-(m+1)} dv`,
with `c_m = (∫_ℂ |t|^(2m) e^{-|t|²} dt) / (∫_{ℂ^(m+1)} e^{-|x|²} dx)`. -/
theorem integral_lastRow {m : ℕ} {Φ : (Fin (m + 1) → ℂ) → ℂ} (hmeas : Measurable Φ)
    {C : ℝ} (hC : ∀ x, ‖Φ x‖ ≤ C) (hΦ : IsHomogeneousZero Φ) :
    ∫ k, Φ (lastRow k) ∂unitaryHaar (m + 1) =
      ((gaussianMoment m / ∫ x : Fin (m + 1) → ℂ, gaussian x : ℝ) : ℂ) *
        ∫ v : Fin m → ℂ, Φ (Fin.snoc v 1) * (chartWeight v : ℂ) := by
  have h1 := integral_mul_gaussian_eq hmeas hC hΦ
  have h2 := integral_mul_gaussian_chart hmeas hC hΦ
  rw [h2, integral_complex_ofReal] at h1
  have hZ : ((∫ x : Fin (m + 1) → ℂ, gaussian x : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast integral_gaussian_pos.ne'
  rw [Complex.ofReal_div]
  field_simp
  rw [h1]

end ComplexLastRowIntegral

open ComplexLastRowIntegral ComplexDuality

/-- **Statement (integrals over `U(m+1)` of functions of the last row).** Let `Φ` be a bounded
measurable complex function on `ℂ^(m+1)` (row vectors) with `Φ(s x) = Φ(x)` for every complex
`s ≠ 0`. Then
`∫_{U(m+1)} Φ(k_{m,·}) dk = c_m ∫_{ℂ^m} Φ(v, 1) (1 + ∑ |vᵢ|²)^{-(m+1)} dv`
(Haar probability measure `unitaryHaar`), where
`c_m = (∫_ℂ |t|^(2m) e^{-|t|²} dt) / (∫_{ℂ^(m+1)} e^{-∑ |xᵢ|²} dx)`. -/
def ComplexLastRowIntegralStatement : Prop :=
  ∀ (m : ℕ) (Φ : (Fin (m + 1) → ℂ) → ℂ), Measurable Φ → (∃ C, ∀ x, ‖Φ x‖ ≤ C) →
    (∀ s : ℂ, s ≠ 0 → ∀ x, Φ (s • x) = Φ x) →
      ∫ k, Φ (((k : Langlands.GeneralLinear (m + 1) ℂ) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (Fin.last m)) ∂unitaryHaar (m + 1) =
        (((∫ t : ℂ, ‖t‖ ^ (2 * m) * Real.exp (-‖t‖ ^ 2)) /
            ∫ x : Fin (m + 1) → ℂ, Real.exp (-∑ i, ‖x i‖ ^ 2) : ℝ) : ℂ) *
          ∫ v : Fin m → ℂ, Φ (Fin.snoc v 1) *
            (((1 + ∑ i, ‖v i‖ ^ 2) ^ (m + 1))⁻¹ : ℝ)

theorem complexLastRowIntegral : ComplexLastRowIntegralStatement := by
  intro m Φ hmeas ⟨C, hC⟩ hΦ
  exact integral_lastRow hmeas hC hΦ

end Langlands.Archimedean
