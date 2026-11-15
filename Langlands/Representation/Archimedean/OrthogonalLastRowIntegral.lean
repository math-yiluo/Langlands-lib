import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Integrals over `O(n)` of functions of the last row
-/

noncomputable section

open MeasureTheory Matrix

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace OrthogonalLastRowIntegral

open RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

local instance borelSpaceK''' (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {n : ℕ}

/-- The squared Euclidean norm `∑ xᵢ²`. -/
def sqNorm (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2

theorem sqNorm_eq_dotProduct (x : Fin n → ℝ) : sqNorm x = x ⬝ᵥ x := by
  simp [sqNorm, dotProduct, sq]

theorem sqNorm_nonneg (x : Fin n → ℝ) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sqNorm_smul (s : ℝ) (x : Fin n → ℝ) : sqNorm (s • x) = s ^ 2 * sqNorm x := by
  simp only [sqNorm, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- Orthogonal matrices preserve the squared norm of row vectors. -/
theorem sqNorm_vecMul {κ : Matrix (Fin n) (Fin n) ℝ} (hκ : κ * κᵀ = 1) (x : Fin n → ℝ) :
    sqNorm (x ᵥ* κ) = sqNorm x := by
  rw [sqNorm_eq_dotProduct, sqNorm_eq_dotProduct, ← dotProduct_mulVec, ← mulVec_transpose,
    mulVec_mulVec, hκ, one_mulVec]

/-- Right multiplication by an orthogonal matrix preserves Lebesgue measure on row vectors. -/
theorem integral_vecMul {κ : Matrix (Fin n) (Fin n) ℝ} (hκ : κ * κᵀ = 1) (g : (Fin n → ℝ) → ℂ) :
    ∫ x, g (x ᵥ* κ) = ∫ x, g x := by
  have hκ' : κᵀ * κ = 1 := by
    have := mul_eq_one_comm.mp hκ
    exact this
  let L : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun x => x ᵥ* κ
      invFun := fun x => x ᵥ* κᵀ
      map_add' := fun x y => add_vecMul κ x y
      map_smul' := fun c x => by simp [smul_vecMul]
      left_inv := fun x => by simp [vecMul_vecMul, hκ]
      right_inv := fun x => by simp [vecMul_vecMul, hκ'] }
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    (LinearEquiv.toContinuousLinearEquiv L).toHomeomorph.toMeasurableEquiv
  have hdet : LinearMap.det (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = κ.det := by
    have : (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = Matrix.toLin' κᵀ := by
      apply LinearMap.ext
      intro x
      simp [L, Matrix.toLin'_apply, mulVec_transpose]
    rw [this, LinearMap.det_toLin', det_transpose]
  have hdet1 : |κ.det| = 1 := by
    have := congrArg Matrix.det hκ
    rw [det_mul, det_transpose, det_one] at this
    have h2 : κ.det ^ 2 = 1 := by rw [sq]; exact this
    rcases sq_eq_one_iff.mp h2 with h | h <;> simp [h]
  have hmap : Measure.map e volume = (volume : Measure (Fin n → ℝ)) := by
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin n → ℝ)))
      (f := (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))) (by rw [hdet]; intro h; simp [h] at hdet1)
    rw [hdet, abs_inv, hdet1, inv_one, ENNReal.ofReal_one, one_smul] at this
    exact this
  have h := integral_map_equiv (μ := (volume : Measure (Fin n → ℝ))) e g
  rw [hmap] at h
  exact h.symm

/-- **Householder reflection.** Every unit row vector is the last row of an orthogonal matrix. -/
theorem exists_orthogonal_lastRow {m : ℕ} (u : Fin (m + 1) → ℝ) (hu : sqNorm u = 1) :
    ∃ κ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ, κ * κᵀ = 1 ∧ κ (Fin.last m) = u := by
  classical
  set e : Fin (m + 1) → ℝ := Pi.single (Fin.last m) 1 with he
  by_cases hue : u = e
  · refine ⟨1, by simp, ?_⟩
    rw [hue]
    funext j
    simp only [he, Matrix.one_apply, Pi.single_apply]
    by_cases h : j = Fin.last m
    · simp [h]
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
  set w := e - u with hw
  have huu : u ⬝ᵥ u = 1 := by rw [← sqNorm_eq_dotProduct, hu]
  have hc_eq : w ⬝ᵥ w = 2 * (1 - u (Fin.last m)) := by
    rw [hw, sub_dotProduct, dotProduct_sub, dotProduct_sub, huu, he, single_dotProduct,
      dotProduct_single, single_dotProduct]
    simp only [Pi.single_eq_same]
    ring
  have hlast : u (Fin.last m) ≠ 1 := by
    intro h1
    apply hue
    have hsum : ∑ i, u i ^ 2 = 1 := hu
    rw [Fin.sum_univ_castSucc, h1, one_pow, add_eq_right] at hsum
    have hzero : ∀ i : Fin m, u i.castSucc = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (u (Fin.castSucc j)))).mp
        hsum i (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [he, h1]
    · rw [hzero i, he, Pi.single_apply, ite_eq_right (Fin.castSucc_lt_last i).ne]
  have hc : w ⬝ᵥ w ≠ 0 := by
    rw [hc_eq]
    intro h
    apply hlast
    linarith [mul_eq_zero.mp h |>.resolve_left two_ne_zero]
  set H : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := 1 - (2 / (w ⬝ᵥ w)) • vecMulVec w w with hH
  refine ⟨H, ?_, ?_⟩
  · have hT : Hᵀ = H := by
      rw [hH, transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec]
    have hVV : vecMulVec w w * vecMulVec w w = (w ⬝ᵥ w) • vecMulVec w w := by
      rw [vecMulVec_mul_vecMulVec]
      ext i j
      simp [vecMulVec_apply, mul_left_comm]
    set a : ℝ := 2 / (w ⬝ᵥ w) with ha
    have hcoef : a * a * (w ⬝ᵥ w) = 2 * a := by
      rw [ha]
      field_simp
    rw [hT, hH]
    calc (1 - a • vecMulVec w w) * (1 - a • vecMulVec w w)
        = 1 - (2 * a - a * a * (w ⬝ᵥ w)) • vecMulVec w w := by
          rw [sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
            Matrix.smul_mul, Matrix.mul_smul, hVV, smul_smul, smul_smul]
          module
      _ = 1 := by rw [hcoef, sub_self, zero_smul, sub_zero]
  · funext j
    have hk : 2 / (w ⬝ᵥ w) * w (Fin.last m) = 1 := by
      rw [hc_eq, hw, he, Pi.sub_apply, Pi.single_eq_same]
      have : (1 : ℝ) - u (Fin.last m) ≠ 0 := sub_ne_zero.mpr (Ne.symm hlast)
      field_simp
    simp only [hH, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    rw [← mul_assoc, hk, one_mul, hw, Pi.sub_apply, Matrix.one_apply, he, Pi.single_apply]
    by_cases h : j = Fin.last m
    · subst h
      simp
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
      ring

/-! ## Averaging over `O(n)` -/

/-- The Gaussian weight `exp(-∑ xᵢ²)`. -/
def gaussian (x : Fin n → ℝ) : ℝ := Real.exp (-sqNorm x)

theorem gaussian_eq_prod (x : Fin n → ℝ) : gaussian x = ∏ i, Real.exp (-1 * x i ^ 2) := by
  rw [gaussian, sqNorm, ← Real.exp_sum]
  congr 1
  simp [Finset.sum_neg_distrib]

theorem integrable_gaussian : Integrable (gaussian (n := n)) := by
  have h := Integrable.fintype_prod (𝕜 := ℝ) (ι := Fin n)
    (f := fun _ t => Real.exp (-1 * t ^ 2)) (μ := fun _ => (volume : Measure ℝ))
    (fun _ => integrable_exp_neg_mul_sq one_pos)
  have : gaussian (n := n) = fun x : Fin n → ℝ => ∏ i, Real.exp (-1 * x i ^ 2) :=
    funext gaussian_eq_prod
  rw [this]
  exact h

/-- The last row of an orthogonal matrix. -/
def lastRow {m : ℕ} (k : unitaryCompact ℝ (m + 1)) : Fin (m + 1) → ℝ :=
  ((k : Langlands.GeneralLinear (m + 1) ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (Fin.last m)

theorem mul_transpose_eq_one {m : ℕ} (k : unitaryCompact ℝ m) :
    ((k : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) *
      ((k : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ)ᵀ = 1 := by
  have := Matrix.mem_unitaryGroup_iff.mp k.2
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this

theorem lastRow_mul {m : ℕ} (k₀ k : unitaryCompact ℝ (m + 1)) :
    lastRow (k₀ * k) = lastRow k₀ ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℝ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) := by
  funext j
  simp only [lastRow, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply, vecMul, dotProduct]

/-- A function of degree-zero homogeneity: `Φ(s x) = Φ(x)` for `s ≠ 0`. -/
def IsHomogeneousZero {m : ℕ} (Φ : (Fin m → ℝ) → ℂ) : Prop :=
  ∀ (s : ℝ), s ≠ 0 → ∀ x, Φ (s • x) = Φ x

/-- For a homogeneous `Φ` and a nonzero row vector `x`, `∫_{O(n)} Φ(x k) dk` is the integral of
`Φ` over the last rows. -/
theorem integral_vecMul_eq {m : ℕ} {Φ : (Fin (m + 1) → ℝ) → ℂ} (hΦ : IsHomogeneousZero Φ)
    {x : Fin (m + 1) → ℝ} (hx : x ≠ 0) :
    ∫ k, Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℝ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) ∂haarK (m + 1) =
      ∫ k, Φ (lastRow k) ∂haarK (m + 1) := by
  have hpos : 0 < sqNorm x := by
    rw [sqNorm_eq_dotProduct]
    exact lt_of_le_of_ne (by rw [← sqNorm_eq_dotProduct]; exact sqNorm_nonneg x)
      (fun h => hx (dotProduct_self_eq_zero.mp h.symm))
  set r := Real.sqrt (sqNorm x) with hr
  have hr0 : r ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  set u := r⁻¹ • x with hu
  have hu1 : sqNorm u = 1 := by
    rw [hu, sqNorm_smul, inv_pow, hr, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  obtain ⟨κ₀, hκ₀, hlast⟩ := exists_orthogonal_lastRow u hu1
  have hκ₀mem : κ₀ ∈ Matrix.unitaryGroup (Fin (m + 1)) ℝ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hκ₀
  let k₀ : unitaryCompact ℝ (m + 1) := ⟨Unitary.toUnits ⟨κ₀, hκ₀mem⟩, hκ₀mem⟩
  have hxu : x = r • lastRow k₀ := by
    have : lastRow k₀ = u := hlast
    rw [this, hu, smul_smul, mul_inv_cancel₀ hr0, one_smul]
  calc ∫ k, Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℝ) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) ∂haarK (m + 1)
      = ∫ k, Φ (lastRow (k₀ * k)) ∂haarK (m + 1) := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        simp only
        rw [hxu, smul_vecMul, hΦ r hr0, lastRow_mul]
    _ = ∫ k, Φ (lastRow k) ∂haarK (m + 1) :=
        integral_mul_left_eq_self (μ := haarK (m + 1)) (fun k => Φ (lastRow k)) k₀

theorem measurable_vecMul_unitary {m : ℕ} :
    Measurable fun p : unitaryCompact ℝ m × (Fin m → ℝ) =>
      p.2 ᵥ* ((p.1 : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) := by
  refine measurable_pi_iff.mpr fun j => ?_
  have hform : (fun p : unitaryCompact ℝ m × (Fin m → ℝ) =>
      (p.2 ᵥ* ((p.1 : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ)) j) =
      fun p => ∑ i, p.2 i * ((p.1 : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) i j :=
    funext fun p => rfl
  rw [hform]
  refine Finset.measurable_sum _ fun i _ => ?_
  have h1 : Measurable fun p : unitaryCompact ℝ m × (Fin m → ℝ) => p.2 i :=
    (measurable_pi_apply i).comp measurable_snd
  have hc : Continuous fun k : unitaryCompact ℝ m =>
      ((k : Langlands.GeneralLinear m ℝ) : Matrix (Fin m) (Fin m) ℝ) i j :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_unitaryCompact_val)
  exact h1.mul (hc.measurable.comp measurable_fst)

/-- **Averaging.** For a bounded measurable homogeneous `Φ`,
`∫ Φ(x) e^{-|x|²} dx = (∫_{O(n)} Φ(last row of k) dk) · ∫ e^{-|x|²} dx`. -/
theorem integral_mul_gaussian_eq {m : ℕ} {Φ : (Fin (m + 1) → ℝ) → ℂ} (hmeas : Measurable Φ)
    {C : ℝ} (hC : ∀ x, ‖Φ x‖ ≤ C) (hΦ : IsHomogeneousZero Φ) :
    ∫ x, Φ x * (gaussian x : ℂ) =
      (∫ k, Φ (lastRow k) ∂haarK (m + 1)) * ∫ x : Fin (m + 1) → ℝ, (gaussian x : ℂ) := by
  set J := ∫ k, Φ (lastRow k) ∂haarK (m + 1)
  have hrot : ∀ k : unitaryCompact ℝ (m + 1), ∫ x, Φ x * (gaussian x : ℂ) =
      ∫ x, Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℝ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) * (gaussian x : ℂ) := by
    intro k
    rw [← integral_vecMul (mul_transpose_eq_one k) (fun x => Φ x * (gaussian x : ℂ))]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [gaussian, sqNorm_vecMul (mul_transpose_eq_one k)]
  have hint : Integrable (Function.uncurry fun (k : unitaryCompact ℝ (m + 1)) (x : Fin (m + 1) → ℝ) =>
      Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℝ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) * (gaussian x : ℂ))
      ((haarK (m + 1)).prod volume) := by
    have hb : Integrable (fun z : unitaryCompact ℝ (m + 1) × (Fin (m + 1) → ℝ) =>
        C * gaussian z.2) ((haarK (m + 1)).prod volume) :=
      (integrable_const C).mul_prod integrable_gaussian
    refine hb.mono' ?_ (ae_of_all _ fun z => ?_)
    · have : Measurable (Function.uncurry fun (k : unitaryCompact ℝ (m + 1))
          (x : Fin (m + 1) → ℝ) => Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℝ) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) * (gaussian x : ℂ)) := by
        refine (hmeas.comp measurable_vecMul_unitary).mul ?_
        exact Complex.measurable_ofReal.comp
          ((Real.continuous_exp.comp (continuous_neg.comp (continuous_finsetSum _
            fun i _ => (continuous_apply i).pow 2))).measurable.comp measurable_snd)
      exact this.aestronglyMeasurable
    · obtain ⟨k, x⟩ := z
      show ‖Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℝ) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) * ((gaussian x : ℝ) : ℂ)‖ ≤ C * gaussian x
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (show 0 ≤ gaussian x from (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_right (hC _) (Real.exp_pos _).le
  calc ∫ x, Φ x * (gaussian x : ℂ)
      = ∫ k : unitaryCompact ℝ (m + 1), (∫ x, Φ x * (gaussian x : ℂ)) ∂haarK (m + 1) := by
        rw [integral_const, probReal_univ, one_smul]
    _ = ∫ k : unitaryCompact ℝ (m + 1), (∫ x, Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℝ) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) * (gaussian x : ℂ)) ∂haarK (m + 1) :=
        integral_congr_ae (ae_of_all _ hrot)
    _ = ∫ x, ∫ k, Φ (x ᵥ* ((k : Langlands.GeneralLinear (m + 1) ℝ) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) * (gaussian x : ℂ) ∂haarK (m + 1) :=
        integral_integral_swap hint
    _ = ∫ x, J * (gaussian x : ℂ) := by
        have hnull : ∀ᵐ x : Fin (m + 1) → ℝ, x ≠ 0 := by
          rw [ae_iff]
          simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
          exact measure_singleton 0
        refine integral_congr_ae (hnull.mono fun x hx => ?_)
        simp only
        rw [integral_mul_const, integral_vecMul_eq hΦ hx]
    _ = J * ∫ x, (gaussian x : ℂ) := integral_const_mul J _

/-! ## The affine chart of the last coordinate -/

/-- The Gaussian moment `∫ |t|^m e^{-t²} dt`. -/
def gaussianMoment (m : ℕ) : ℝ := ∫ t : ℝ, |t| ^ m * Real.exp (-t ^ 2)

theorem integrable_abs_pow_mul_exp (m : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable fun t : ℝ => |t| ^ m * Real.exp (-(a * t ^ 2)) := by
  have hm : (-1 : ℝ) < m := by
    have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    linarith
  have h := (integrable_rpow_mul_exp_neg_mul_sq ha hm).norm
  refine h.congr (ae_of_all _ fun t => ?_)
  simp only [Real.norm_eq_abs, abs_mul, Real.rpow_natCast, abs_pow, abs_of_pos (Real.exp_pos _),
    neg_mul]

theorem integral_abs_pow_mul_exp_scale (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ, |t| ^ m * Real.exp (-(a * t ^ 2)) =
      (Real.sqrt a ^ (m + 1))⁻¹ * gaussianMoment m := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have h := Measure.integral_comp_mul_left (fun t : ℝ => |t| ^ m * Real.exp (-t ^ 2))
    (Real.sqrt a)
  have hpt : ∀ x : ℝ, |Real.sqrt a * x| ^ m * Real.exp (-(Real.sqrt a * x) ^ 2) =
      Real.sqrt a ^ m * (|x| ^ m * Real.exp (-(a * x ^ 2))) := fun x => by
    rw [abs_mul, abs_of_pos hs, mul_pow, mul_pow, Real.sq_sqrt ha.le]
    ring
  simp only [hpt] at h
  rw [integral_const_mul, abs_of_pos (inv_pos.mpr hs), smul_eq_mul] at h
  have hne : Real.sqrt a ^ m ≠ 0 := pow_ne_zero _ hs.ne'
  rw [gaussianMoment, pow_succ, mul_inv, mul_assoc, ← h]
  field_simp

theorem snoc_smul_one {m : ℕ} (s : ℝ) (v : Fin m → ℝ) :
    (Fin.snoc (s • v) s : Fin (m + 1) → ℝ) = s • (Fin.snoc v 1 : Fin (m + 1) → ℝ) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · simp

theorem sqNorm_snoc {m : ℕ} (v : Fin m → ℝ) (s : ℝ) :
    sqNorm (Fin.snoc v s : Fin (m + 1) → ℝ) = sqNorm v + s ^ 2 := by
  simp [sqNorm, Fin.sum_univ_castSucc]

/-- The chart weight `(1 + |v|²)^{-(m+1)/2}`. -/
def chartWeight {m : ℕ} (v : Fin m → ℝ) : ℝ := (Real.sqrt (1 + sqNorm v) ^ (m + 1))⁻¹

theorem norm_sq_le_sqNorm {m : ℕ} (v : Fin m → ℝ) : ‖v‖ ^ 2 ≤ sqNorm v := by
  have h : ‖v‖ ≤ Real.sqrt (sqNorm v) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => v j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  calc ‖v‖ ^ 2 ≤ Real.sqrt (sqNorm v) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = sqNorm v := Real.sq_sqrt (sqNorm_nonneg v)

theorem chartWeight_nonneg {m : ℕ} (v : Fin m → ℝ) : 0 ≤ chartWeight v :=
  inv_nonneg.mpr (pow_nonneg (Real.sqrt_nonneg _) _)

theorem integrable_chartWeight {m : ℕ} : Integrable (chartWeight (m := m)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := Fin m → ℝ) (μ := volume)
    (r := (m : ℝ) + 1) (by simp)
  refine h.mono' ?_ (ae_of_all _ fun v => ?_)
  · have hc : Continuous (chartWeight (m := m)) := by
      unfold chartWeight
      refine Continuous.inv₀ ((Real.continuous_sqrt.comp (continuous_const.add
        (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2))).pow _) fun v => ?_
      exact pow_ne_zero _ (Real.sqrt_pos.mpr (by linarith [sqNorm_nonneg v])).ne'
    exact hc.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (chartWeight_nonneg v), chartWeight]
    have h1 : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by positivity
    have h2 : 1 + ‖v‖ ^ 2 ≤ 1 + sqNorm v := by linarith [norm_sq_le_sqNorm v]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith [sqNorm_nonneg v]),
      ← Real.rpow_neg (by linarith [sqNorm_nonneg v])]
    have : -(1 / 2 * ((m + 1 : ℕ) : ℝ)) = -((m : ℝ) + 1) / 2 := by push_cast; ring
    rw [this]
    exact Real.rpow_le_rpow_of_nonpos h1 h2 (by
      have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
      linarith)

theorem measurable_snoc {m : ℕ} :
    Measurable fun p : ℝ × (Fin m → ℝ) => (Fin.snoc p.2 p.1 : Fin (m + 1) → ℝ) := by
  refine measurable_pi_iff.mpr fun j => ?_
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have : (fun p : ℝ × (Fin m → ℝ) => (Fin.snoc p.2 p.1 : Fin (m + 1) → ℝ) (Fin.last m)) =
        fun p => p.1 := funext fun p => by simp
    rw [this]
    exact measurable_fst
  · have : (fun p : ℝ × (Fin m → ℝ) => (Fin.snoc p.2 p.1 : Fin (m + 1) → ℝ) i.castSucc) =
        fun p => p.2 i := funext fun p => by simp
    rw [this]
    exact (measurable_pi_apply i).comp measurable_snd

/-- **Chart.** For a bounded measurable homogeneous `Φ`,
`∫ Φ(x) e^{-|x|²} dx = (∫ |t|^m e^{-t²} dt) · ∫ Φ(v, 1) (1 + |v|²)^{-(m+1)/2} dv`. -/
theorem integral_mul_gaussian_chart {m : ℕ} {Φ : (Fin (m + 1) → ℝ) → ℂ} (hmeas : Measurable Φ)
    {C : ℝ} (hC : ∀ x, ‖Φ x‖ ≤ C) (hΦ : IsHomogeneousZero Φ) :
    ∫ x, Φ x * (gaussian x : ℂ) =
      (gaussianMoment m : ℂ) * ∫ v : Fin m → ℝ, Φ (Fin.snoc v 1) * (chartWeight v : ℂ) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m) with he
  have hp : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
  set G : ℝ × (Fin m → ℝ) → ℂ := fun p =>
    Φ (Fin.snoc p.2 p.1) * (gaussian (Fin.snoc p.2 p.1 : Fin (m + 1) → ℝ) : ℂ) with hG
  have hsnoc : ∀ x : Fin (m + 1) → ℝ, (Fin.snoc (e x).2 (e x).1 : Fin (m + 1) → ℝ) = x := by
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
  have hintF : Integrable (fun x : Fin (m + 1) → ℝ => Φ x * (gaussian x : ℂ)) := by
    refine (integrable_gaussian.ofReal (𝕜 := ℂ)).bdd_mul hmeas.aestronglyMeasurable
      (ae_of_all _ hC) |>.congr (ae_of_all _ fun x => ?_)
    simp
  have hintG : Integrable G (volume.prod volume) := by
    rw [← hp.integrable_comp_emb e.measurableEmbedding, ← hFG]
    exact hintF
  -- the inner integral over `y`
  have hinner : ∀ s : ℝ, s ≠ 0 → ∫ y, G (s, y) =
      ((|s| ^ m : ℝ) : ℂ) * ∫ v : Fin m → ℝ, Φ (Fin.snoc v 1) *
        ((Real.exp (-((1 + sqNorm v) * s ^ 2))) : ℂ) := by
    intro s hs
    have hsc := Measure.integral_comp_smul (μ := (volume : Measure (Fin m → ℝ)))
      (fun y => G (s, y)) s
    rw [Module.finrank_fin_fun] at hsc
    have hval : ∀ v : Fin m → ℝ, G (s, s • v) = Φ (Fin.snoc v 1) *
        ((Real.exp (-((1 + sqNorm v) * s ^ 2))) : ℂ) := by
      intro v
      simp only [hG, snoc_smul_one, hΦ s hs, gaussian, sqNorm_smul, sqNorm_snoc]
      congr 3
      simp [sqNorm]
      ring
    simp only [hval] at hsc
    have hk : (|s| ^ m : ℝ) * |(s ^ m)⁻¹| = 1 := by
      rw [abs_inv, abs_pow, mul_inv_cancel₀ (pow_ne_zero _ (abs_ne_zero.mpr hs))]
    rw [hsc, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hk, Complex.ofReal_one,
      one_mul]
  -- the integrand after the inner substitution
  set H : ℝ × (Fin m → ℝ) → ℂ := fun p => Φ (Fin.snoc p.2 1) *
    ((|p.1| ^ m * Real.exp (-((1 + sqNorm p.2) * p.1 ^ 2)) : ℝ) : ℂ) with hH
  have hHmeas : Measurable H := by
    refine (hmeas.comp (measurable_snoc.comp (measurable_const.prodMk measurable_snd))).mul ?_
    refine Complex.measurable_ofReal.comp ?_
    have hc : Continuous fun p : ℝ × (Fin m → ℝ) =>
        |p.1| ^ m * Real.exp (-((1 + sqNorm p.2) * p.1 ^ 2)) := by
      unfold sqNorm
      fun_prop
    exact hc.measurable
  have hintH : Integrable H (volume.prod volume) := by
    rw [integrable_prod_iff' hHmeas.aestronglyMeasurable]
    have hs_int : ∀ v : Fin m → ℝ, Integrable fun s : ℝ =>
        |s| ^ m * Real.exp (-((1 + sqNorm v) * s ^ 2)) := fun v =>
      integrable_abs_pow_mul_exp m (by linarith [sqNorm_nonneg v])
    refine ⟨ae_of_all _ fun v => ?_, ?_⟩
    · show Integrable (fun s : ℝ => Φ (Fin.snoc v 1) *
        ((|s| ^ m * Real.exp (-((1 + sqNorm v) * s ^ 2)) : ℝ) : ℂ))
      exact ((hs_int v).ofReal (𝕜 := ℂ)).const_mul _
    have heq : (fun v : Fin m → ℝ => ∫ s, ‖H (s, v)‖) =
        fun v => ‖Φ (Fin.snoc v 1)‖ * (chartWeight v * gaussianMoment m) := by
      funext v
      have hn : ∀ s : ℝ, ‖H (s, v)‖ = ‖Φ (Fin.snoc v 1)‖ *
          (|s| ^ m * Real.exp (-((1 + sqNorm v) * s ^ 2))) := fun s => by
        show ‖Φ (Fin.snoc v 1) * ((|s| ^ m * Real.exp (-((1 + sqNorm v) * s ^ 2)) : ℝ) : ℂ)‖ = _
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
          (mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le)]
      rw [integral_congr_ae (ae_of_all _ hn), integral_const_mul,
        integral_abs_pow_mul_exp_scale m (by linarith [sqNorm_nonneg v]), chartWeight]
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
        have hnull : ∀ᵐ s : ℝ, s ≠ 0 := by
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
    _ = ∫ v : Fin m → ℝ, (gaussianMoment m : ℂ) * (Φ (Fin.snoc v 1) * (chartWeight v : ℂ)) := by
        refine integral_congr_ae (ae_of_all _ fun v => ?_)
        simp only [hH]
        rw [integral_const_mul, integral_complex_ofReal,
          integral_abs_pow_mul_exp_scale m (by linarith [sqNorm_nonneg v]), chartWeight]
        push_cast
        ring
    _ = (gaussianMoment m : ℂ) * ∫ v : Fin m → ℝ, Φ (Fin.snoc v 1) * (chartWeight v : ℂ) :=
        integral_const_mul _ _

theorem integral_gaussian_pos {m : ℕ} : 0 < ∫ x : Fin m → ℝ, gaussian x := by
  have hpos : ∀ x : Fin m → ℝ, 0 < gaussian x := fun x => Real.exp_pos _
  rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) integrable_gaussian]
  have : Function.support (gaussian (n := m)) = Set.univ :=
    Set.eq_univ_of_forall fun x => (hpos x).ne'
  rw [this, Measure.measure_univ_pos]
  exact NeZero.ne _

/-- **Last-row formula.** For a bounded measurable `Φ` on row vectors with `Φ(s x) = Φ(x)` for
`s ≠ 0`, `∫_{O(m+1)} Φ(last row of k) dk = c_m ∫_{ℝ^m} Φ(v, 1) (1 + |v|²)^{-(m+1)/2} dv`, with
`c_m = (∫ |t|^m e^{-t²} dt) / (∫_{ℝ^{m+1}} e^{-|x|²} dx)`. -/
theorem integral_lastRow {m : ℕ} {Φ : (Fin (m + 1) → ℝ) → ℂ} (hmeas : Measurable Φ)
    {C : ℝ} (hC : ∀ x, ‖Φ x‖ ≤ C) (hΦ : IsHomogeneousZero Φ) :
    ∫ k, Φ (lastRow k) ∂haarK (m + 1) =
      ((gaussianMoment m / ∫ x : Fin (m + 1) → ℝ, gaussian x : ℝ) : ℂ) *
        ∫ v : Fin m → ℝ, Φ (Fin.snoc v 1) * (chartWeight v : ℂ) := by
  have h1 := integral_mul_gaussian_eq hmeas hC hΦ
  have h2 := integral_mul_gaussian_chart hmeas hC hΦ
  rw [h2, integral_complex_ofReal] at h1
  have hZ : ((∫ x : Fin (m + 1) → ℝ, gaussian x : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast integral_gaussian_pos.ne'
  rw [Complex.ofReal_div]
  field_simp
  rw [h1]

end OrthogonalLastRowIntegral

open OrthogonalLastRowIntegral RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

/-- **Statement (integrals over `O(m+1)` of functions of the last row).** Let `Φ` be a bounded
measurable complex function on `ℝ^{m+1}` (row vectors) with `Φ(s x) = Φ(x)` for every real
`s ≠ 0`. Then
`∫_{O(m+1)} Φ(k_{m,·}) dk = c_m ∫_{ℝ^m} Φ(v, 1) (1 + ∑ vᵢ²)^{-(m+1)/2} dv`
(normalized Haar measure `haarK`), where
`c_m = (∫_ℝ |t|^m e^{-t²} dt) / (∫_{ℝ^{m+1}} e^{-∑ xᵢ²} dx)`. -/
def OrthogonalLastRowIntegralStatement : Prop :=
  ∀ (m : ℕ) (Φ : (Fin (m + 1) → ℝ) → ℂ), Measurable Φ → (∃ C, ∀ x, ‖Φ x‖ ≤ C) →
    (∀ s : ℝ, s ≠ 0 → ∀ x, Φ (s • x) = Φ x) →
      ∫ k, Φ (((k : Langlands.GeneralLinear (m + 1) ℝ) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (Fin.last m)) ∂haarK (m + 1) =
        (((∫ t : ℝ, |t| ^ m * Real.exp (-t ^ 2)) /
            ∫ x : Fin (m + 1) → ℝ, Real.exp (-∑ i, x i ^ 2) : ℝ) : ℂ) *
          ∫ v : Fin m → ℝ, Φ (Fin.snoc v 1) *
            (((Real.sqrt (1 + ∑ i, v i ^ 2)) ^ (m + 1))⁻¹ : ℝ)

theorem orthogonalLastRowIntegral : OrthogonalLastRowIntegralStatement := by
  intro m Φ hmeas ⟨C, hC⟩ hΦ
  exact integral_lastRow hmeas hC hΦ

end Langlands.Archimedean
