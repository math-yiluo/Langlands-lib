import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.Representation.Archimedean.PrincipalSeriesMatrixCoefficientAnalytic

/-!
# `GL_n(ℝ)`-invariance of the `O(n)`-integral on modulus-equivariant functions
-/

noncomputable section

open MeasureTheory Metric

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

-- The charts on units need reduction through the normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

namespace KIntegralInvariance

open RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

local instance borelSpaceK'' (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {n : ℕ}

theorem isModulusEquivariant_rightTranslation {φ : Langlands.GeneralLinear n ℝ → ℂ}
    (hφ : IsModulusEquivariant φ) (h : Langlands.GeneralLinear n ℝ) :
    IsModulusEquivariant (fun x => φ (x * h)) := fun x u g => by
  simp only
  rw [mul_assoc _ g h, hφ]

theorem matrixExpUnit_conj (h : Langlands.GeneralLinear n ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (s : ℝ) :
    matrixExpUnit n (s • ((h : Matrix (Fin n) (Fin n) ℝ) * X *
        ((h⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ))) =
      h * matrixExpUnit n (s • X) * h⁻¹ := by
  apply Units.ext
  rw [matrixExpUnit_val, Units.val_mul, Units.val_mul, matrixExpUnit_val]
  have hinv : ((h⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      (h : Matrix (Fin n) (Fin n) ℝ)⁻¹ := by
    rw [Matrix.coe_units_inv]
  have hsm : s • ((h : Matrix (Fin n) (Fin n) ℝ) * X * (h : Matrix (Fin n) (Fin n) ℝ)⁻¹) =
      (h : Matrix (Fin n) (Fin n) ℝ) * (s • X) * (h : Matrix (Fin n) (Fin n) ℝ)⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hinv, hsm, Matrix.exp_conj _ _ (Units.isUnit h)]

/-- The right derivative at `k h` along `X` is the right derivative at `k` of the translate by
`h` along `h X h⁻¹`. -/
theorem rightDerivative_mul_eq {φ : Langlands.GeneralLinear n ℝ → ℂ}
    (hφ : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ φ) (h k : Langlands.GeneralLinear n ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    rightDerivative (matrixModel ℝ n) X φ (k * h) =
      rightDerivative (matrixModel ℝ n) ((h : Matrix (Fin n) (Fin n) ℝ) * X *
        ((h⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) (fun x => φ (x * h)) k := by
  have h1 := hasDerivAt_mul_matrixExpUnit_smul (hφ.of_le (by norm_num)) (k * h) X
  have h2 := hasDerivAt_mul_matrixExpUnit_smul
    ((hφ.comp contMDiff_mul_right).of_le (by norm_num) :
      ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) 1 (fun x => φ (x * h))) k
    ((h : Matrix (Fin n) (Fin n) ℝ) * X *
      ((h⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ))
  refine h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_))
  simp only [Function.comp_apply]
  rw [matrixExpUnit_conj]
  congr 1
  group

theorem hasDerivAt_mul_matrixExpUnit_at {φ : Langlands.GeneralLinear n ℝ → ℂ}
    (hφ : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ φ) (x : Langlands.GeneralLinear n ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun s => φ (x * matrixExpUnit n (s • X)))
      (rightDerivative (matrixModel ℝ n) X φ (x * matrixExpUnit n (t • X))) t := by
  have h0 : HasDerivAt (fun s => φ (x * matrixExpUnit n (t • X) * matrixExpUnit n (s • X)))
      (rightDerivative (matrixModel ℝ n) X φ (x * matrixExpUnit n (t • X))) (t - t) := by
    rw [sub_self]
    exact hasDerivAt_mul_matrixExpUnit_smul (hφ.of_le (by norm_num)) _ X
  convert HasDerivAt.comp_sub_const t t h0 using 1
  funext s
  rw [mul_assoc, ← matrixExpUnit_add_smul, add_sub_cancel]

theorem continuous_matrixExpUnit_smul (X : Matrix (Fin n) (Fin n) ℝ) :
    Continuous fun s : ℝ => matrixExpUnit n (s • X) :=
  (contMDiff_matrixExpUnit_smul n X).continuous

/-- The `O(n)`-integral of a translate along a one-parameter subgroup has derivative zero. -/
theorem integral_mul_matrixExpUnit_eq {φ : Langlands.GeneralLinear n ℝ → ℂ}
    (hφ : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ φ) (hmod : IsModulusEquivariant φ)
    (g : Langlands.GeneralLinear n ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    ∫ k, φ ((k : Langlands.GeneralLinear n ℝ) * g * matrixExpUnit n (t • X)) ∂haarK n =
      ∫ k, φ ((k : Langlands.GeneralLinear n ℝ) * g) ∂haarK n := by
  set ψ : ℝ → ℂ := fun t =>
    ∫ k, φ ((k : Langlands.GeneralLinear n ℝ) * g * matrixExpUnit n (t • X)) ∂haarK n
  have hR := contMDiff_rightDerivative hφ X
  have hderiv : ∀ t₀ : ℝ, HasDerivAt ψ 0 t₀ := by
    intro t₀
    have hcontF : ∀ t : ℝ, Continuous fun k : unitaryCompact ℝ n =>
        φ ((k : Langlands.GeneralLinear n ℝ) * g * matrixExpUnit n (t • X)) := fun t =>
      hφ.continuous.comp ((continuous_subtype_val.mul continuous_const).mul continuous_const)
    have hjoint : Continuous fun p : ℝ × unitaryCompact ℝ n =>
        rightDerivative (matrixModel ℝ n) X φ
          ((p.2 : Langlands.GeneralLinear n ℝ) * g * matrixExpUnit n (p.1 • X)) :=
      hR.continuous.comp (((continuous_subtype_val.comp continuous_snd).mul continuous_const).mul
        ((continuous_matrixExpUnit_smul X).comp continuous_fst))
    obtain ⟨C, hC⟩ := ((isCompact_closedBall t₀ 1).prod isCompact_univ).exists_bound_of_continuousOn
      hjoint.continuousOn
    have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := haarK n)
      (F := fun t (k : unitaryCompact ℝ n) =>
        φ ((k : Langlands.GeneralLinear n ℝ) * g * matrixExpUnit n (t • X)))
      (F' := fun t (k : unitaryCompact ℝ n) => rightDerivative (matrixModel ℝ n) X φ
        ((k : Langlands.GeneralLinear n ℝ) * g * matrixExpUnit n (t • X)))
      (bound := fun _ => C) (ball_mem_nhds t₀ one_pos)
      (Filter.Eventually.of_forall fun t => (hcontF t).aestronglyMeasurable)
      (integrable_of_continuous (hcontF t₀))
      ((hjoint.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (ae_of_all _ fun k t ht => hC (t, k) ⟨ball_subset_closedBall ht, Set.mem_univ k⟩)
      (integrable_const C)
      (ae_of_all _ fun k t _ => hasDerivAt_mul_matrixExpUnit_at hφ _ X t)
    have hzero : ∫ k, rightDerivative (matrixModel ℝ n) X φ
        ((k : Langlands.GeneralLinear n ℝ) * g * matrixExpUnit n (t₀ • X)) ∂haarK n = 0 := by
      have hpt : ∀ k : unitaryCompact ℝ n, rightDerivative (matrixModel ℝ n) X φ
          ((k : Langlands.GeneralLinear n ℝ) * g * matrixExpUnit n (t₀ • X)) =
          rightDerivative (matrixModel ℝ n)
            (((g * matrixExpUnit n (t₀ • X) : Langlands.GeneralLinear n ℝ) :
              Matrix (Fin n) (Fin n) ℝ) * X *
              (((g * matrixExpUnit n (t₀ • X))⁻¹ : Langlands.GeneralLinear n ℝ) :
                Matrix (Fin n) (Fin n) ℝ))
            (fun x => φ (x * (g * matrixExpUnit n (t₀ • X)))) (k : Langlands.GeneralLinear n ℝ) :=
        fun k => by
          rw [mul_assoc]
          exact rightDerivative_mul_eq hφ _ _ X
      rw [integral_congr_ae (ae_of_all _ hpt)]
      exact integral_rightDerivative_eq_zero (hφ.comp contMDiff_mul_right)
        (isModulusEquivariant_rightTranslation hmod _) _
    rw [hzero] at hD
    exact hD.2
  have hconst := is_const_of_deriv_eq_zero (fun t => (hderiv t).differentiableAt)
    (fun t => (hderiv t).deriv) t 0
  simp only [ψ, zero_smul, matrixExpUnit_zero, mul_one] at hconst
  exact hconst

theorem expDiagonal_one_eq (h : Fin n → ℝ) :
    MatrixCoefficientAnalytic.expDiagonal h 1 = matrixExpUnit n ((1 : ℝ) • Matrix.diagonal h) := by
  rw [one_smul, matrixExpUnit_diagonal]
  apply Units.ext
  rw [MatrixCoefficientAnalytic.expDiagonal_val, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val]
  congr 1
  funext i
  simp

/-- **`GL_n(ℝ)`-invariance of the `O(n)`-integral.** -/
theorem integral_mul_eq {φ : Langlands.GeneralLinear n ℝ → ℂ}
    (hφ : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ φ) (hmod : IsModulusEquivariant φ)
    (g : Langlands.GeneralLinear n ℝ) :
    ∫ k, φ ((k : Langlands.GeneralLinear n ℝ) * g) ∂haarK n =
      ∫ k, φ (k : Langlands.GeneralLinear n ℝ) ∂haarK n := by
  obtain ⟨k₁, hk₁, k₂, hk₂, h, rfl⟩ := MatrixCoefficientAnalytic.exists_kak g
  set φ₂ : Langlands.GeneralLinear n ℝ → ℂ := fun x => φ (x * k₂) with hφ₂
  have hφ₂s : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ φ₂ := hφ.comp contMDiff_mul_right
  have hφ₂m : IsModulusEquivariant φ₂ := isModulusEquivariant_rightTranslation hmod k₂
  calc ∫ k, φ ((k : Langlands.GeneralLinear n ℝ) *
        (k₁ * MatrixCoefficientAnalytic.expDiagonal h 1 * k₂)) ∂haarK n
      = ∫ k, φ₂ ((k : Langlands.GeneralLinear n ℝ) * k₁ *
          matrixExpUnit n ((1 : ℝ) • Matrix.diagonal h)) ∂haarK n := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        simp only [φ₂, expDiagonal_one_eq, mul_assoc]
    _ = ∫ k, φ₂ ((k : Langlands.GeneralLinear n ℝ) * k₁) ∂haarK n :=
        integral_mul_matrixExpUnit_eq hφ₂s hφ₂m k₁ _ 1
    _ = ∫ k, φ₂ (k : Langlands.GeneralLinear n ℝ) ∂haarK n :=
        integral_mul_right_eq_self (μ := haarK n)
          (fun k : unitaryCompact ℝ n => φ₂ (k : Langlands.GeneralLinear n ℝ)) ⟨k₁, hk₁⟩
    _ = ∫ k, φ (k : Langlands.GeneralLinear n ℝ) ∂haarK n :=
        integral_mul_right_eq_self (μ := haarK n)
          (fun k : unitaryCompact ℝ n => φ (k : Langlands.GeneralLinear n ℝ)) ⟨k₂, hk₂⟩

end KIntegralInvariance

open RealPrincipalSeriesDuality

attribute [local instance] measurableSpaceK

/-- **Statement (`GL_n(ℝ)`-invariance of the `O(n)`-integral).** For every smooth function `φ` on
`GL_n(ℝ)` that transforms on the left by the modulus character of the upper triangular Borel
subgroup (`IsModulusEquivariant`), and every `g ∈ GL_n(ℝ)`,
`∫_{O(n)} φ(k g) dk = ∫_{O(n)} φ(k) dk` for the normalized Haar measure `haarK n`. -/
def KIntegralInvarianceStatement : Prop :=
  ∀ (n : ℕ) (φ : Langlands.GeneralLinear n ℝ → ℂ),
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ φ → IsModulusEquivariant φ →
      ∀ g : Langlands.GeneralLinear n ℝ,
        ∫ k, φ ((k : Langlands.GeneralLinear n ℝ) * g) ∂haarK n =
          ∫ k, φ (k : Langlands.GeneralLinear n ℝ) ∂haarK n

theorem kIntegralInvariance : KIntegralInvarianceStatement :=
  fun _ _ hφ hmod g => KIntegralInvariance.integral_mul_eq hφ hmod g

end Langlands.Archimedean
