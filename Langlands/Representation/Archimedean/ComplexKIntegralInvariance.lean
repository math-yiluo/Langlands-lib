import Langlands.Representation.Archimedean.ComplexMatrixCoefficientAnalytic
import Langlands.Representation.Archimedean.ComplexDuality.LieInvariance
import Langlands.Representation.Archimedean.ComplexDuality.UnitaryHaar

/-!
# `GL_n(ℂ)`-invariance of the `U(n)`-integral on modulus-equivariant functions

For every smooth function `φ` on `GL_n(ℂ)` transforming on the left under the upper triangular
Borel subgroup by its modulus character, `∫_{U(n)} φ(k g) dk = ∫_{U(n)} φ(k) dk` for every
`g ∈ GL_n(ℂ)`. The infinitesimal version is the Library's pointwise identity of
`ComplexDuality.LieInvariance`, here integrated for a general modulus-equivariant function; it
is then integrated along real diagonal one-parameter subgroups and combined with the `KAK`
decomposition.
-/

noncomputable section

open MeasureTheory Metric Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator ComplexConjugate

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false

-- The charts on units need reduction through the normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

namespace ComplexKIntegralInvariance

open ComplexDuality ComplexDuality.LieInvariance

variable {n : ℕ}

/-- The characters `z ↦ (|z|²)^((n-1)/2 - i)`: the principal series of these characters consists
of the smooth functions transforming on the left by the modulus character
`diag(a) u ↦ ∏ᵢ |aᵢ|^(2(n-1-2i))` of the upper triangular Borel subgroup. -/
def modulusCharacter (n : ℕ) : ℕ → ℂˣ → ℂ :=
  fun i z => ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))

/-! ## Infinitesimal invariance for a general modulus-equivariant function -/

section Infinitesimal

variable [MeasurableSpace (unitaryCompact ℂ n)] [BorelSpace (unitaryCompact ℂ n)]
  (μ : Measure (unitaryCompact ℂ n))

/-- **Infinitesimal invariance.** Let `Φ` be smooth on the invertible matrices, invariant under
left multiplication by upper unipotent matrices and transforming under left multiplication by the
diagonal torus by the modulus character. Then `∫_{U(n)} DΦ(k)(k X) dk = 0` for every complex
matrix `X` and every left-invariant finite measure on `U(n)`. -/
theorem integral_fderiv_eq_zero [μ.IsMulLeftInvariant] [IsFiniteMeasure μ]
    {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : ContDiffOn ℝ ∞ Φ {y | IsUnit y})
    (hunip : ∀ y : Matrix (Fin n) (Fin n) ℂ, IsUnit y → ∀ u : upperUnipotent n ℂ,
      Φ (((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) * y) = Φ y)
    (hdiag : ∀ y : Matrix (Fin n) (Fin n) ℂ, IsUnit y → ∀ a : Fin n → ℂˣ,
      Φ (Matrix.diagonal (fun i => (a i : ℂ)) * y) =
        (∏ i : Fin n, ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) *
          ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))) * Φ y)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    ∫ k, fderiv ℝ Φ ((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)
      (((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) * X) ∂μ = 0 := by
  let kv : unitaryCompact ℂ n → Matrix (Fin n) (Fin n) ℂ := fun k =>
    ((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)
  have hΦd : ∀ k : unitaryCompact ℂ n, DifferentiableAt ℝ Φ (kv k) :=
    fun k => (hΦ.differentiableOn (by simp)).differentiableAt
      (isOpen_setOf_isUnit_matrix.mem_nhds (Units.isUnit _))
  have hkk : ∀ k : unitaryCompact ℂ n, star (kv k) * kv k = 1 := fun k =>
    Matrix.mem_unitaryGroup_iff'.mp k.2
  have hpt : ∀ k : unitaryCompact ℂ n,
      fderiv ℝ Φ (kv k) (kv k * X) =
      ∑ a : Fin n, ∑ b : Fin n, if b < a then pairTerm Φ X (kv k) a b else 0 := fun k =>
    fderiv_mul_eq_sum_pairTerm (hΦd k) (hunip _ (Units.isUnit _)) (hdiag _ (Units.isUnit _))
      (hkk k) X
  have hRe : ∀ a b : Fin n, ContDiffOn ℝ 1
      (fun y => coeffRe X a b y * Φ y) {y | IsUnit y} := fun a b =>
    contDiffOn_one_of_infty ((contDiff_coeffRe X a b).contDiffOn.mul hΦ)
  have hIm : ∀ a b : Fin n, ContDiffOn ℝ 1
      (fun y => coeffIm X a b y * Φ y) {y | IsUnit y} := fun a b =>
    contDiffOn_one_of_infty ((contDiff_coeffIm X a b).contDiffOn.mul hΦ)
  have hcont : ∀ a b : Fin n, Continuous fun k : unitaryCompact ℂ n =>
      if b < a then pairTerm Φ X (kv k) a b else 0 := fun a b => by
    by_cases hba : b < a
    · simp only [hba, ite_true, pairTerm]
      exact (continuous_fderiv_apply_val (hRe a b)
          (V := fun y => skewRe a b * y) (continuous_const.mul continuous_id)).add
        (continuous_fderiv_apply_val (hIm a b)
          (V := fun y => skewIm a b * y) (continuous_const.mul continuous_id))
    · simp only [hba, ite_false]
      exact continuous_const
  have hint : ∀ a b : Fin n, ∫ k, (if b < a then pairTerm Φ X (kv k) a b else 0) ∂μ = 0 :=
    fun a b => by
      by_cases hba : b < a
      · simp only [hba, ite_true, pairTerm]
        have hY1 : (skewRe a b)ᴴ = -skewRe a b := by
          rw [← Matrix.star_eq_conjTranspose, star_skewRe]
        have hY2 : (skewIm a b)ᴴ = -skewIm a b := by
          rw [← Matrix.star_eq_conjTranspose, star_skewIm]
        rw [integral_add
          (integrable_of_continuous μ
            (continuous_fderiv_apply_val (hRe a b)
            (V := fun y => skewRe a b * y) (continuous_const.mul continuous_id)))
          (integrable_of_continuous μ
            (continuous_fderiv_apply_val (hIm a b)
            (V := fun y => skewIm a b * y) (continuous_const.mul continuous_id))),
          integral_fderiv_mul_eq_zero μ (hRe a b) hY1, integral_fderiv_mul_eq_zero μ (hIm a b) hY2,
          add_zero]
      · simp [hba]
  change ∫ k, fderiv ℝ Φ (kv k) (kv k * X) ∂μ = 0
  simp only [hpt]
  rw [integral_finsetSum _ fun a _ => integrable_of_continuous μ
    (continuous_finsetSum _ fun b _ => hcont a b)]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => integrable_of_continuous μ (hcont a b)]
  exact Finset.sum_eq_zero fun b _ => hint a b

end Infinitesimal

/-! ## Translates of modulus-equivariant functions -/

theorem modulus_mul_eq (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n (modulusCharacter n) a =
      ∏ i : Fin n, ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) *
        ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) := by
  simp [principalSeriesCharacter, modulusCharacter, Complex.finrank_real_complex]

/-- The extension `y ↦ φ(y g)` of a translate, as a function of matrices. -/
def translateExtension (φ : Langlands.GeneralLinear n ℂ → ℂ) (g : Langlands.GeneralLinear n ℂ)
    (y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  unitsExtension φ (y * (g : Matrix (Fin n) (Fin n) ℂ))

theorem isUnit_mul_val {y : Matrix (Fin n) (Fin n) ℂ} (hy : IsUnit y)
    (g : Langlands.GeneralLinear n ℂ) : IsUnit (y * (g : Matrix (Fin n) (Fin n) ℂ)) :=
  hy.mul (Units.isUnit g)

theorem translateExtension_contDiffOn {φ : Langlands.GeneralLinear n ℂ → ℂ}
    (hφ : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ φ) (g : Langlands.GeneralLinear n ℂ) :
    ContDiffOn ℝ ∞ (translateExtension φ g) {y | IsUnit y} := by
  have hm : ContDiff ℝ ∞ fun y : Matrix (Fin n) (Fin n) ℂ =>
      y * (g : Matrix (Fin n) (Fin n) ℂ) :=
    (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)).flip
      (g : Matrix (Fin n) (Fin n) ℂ) |>.contDiff
  exact (contDiffOn_unitsExtension hφ).comp hm.contDiffOn fun y hy => isUnit_mul_val hy g

theorem translateExtension_unit {φ : Langlands.GeneralLinear n ℂ → ℂ}
    (g x : Langlands.GeneralLinear n ℂ) :
    translateExtension φ g (x : Matrix (Fin n) (Fin n) ℂ) = φ (x * g) := by
  rw [translateExtension, ← Units.val_mul, unitsExtension_val]

theorem translateExtension_unipotent {φ : Langlands.GeneralLinear n ℂ → ℂ}
    (hφ : φ ∈ principalSeries ℂ n (modulusCharacter n)) (g : Langlands.GeneralLinear n ℂ)
    {y : Matrix (Fin n) (Fin n) ℂ} (hy : IsUnit y) (u : upperUnipotent n ℂ) :
    translateExtension φ g (((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) * y) =
      translateExtension φ g y := by
  obtain ⟨x, rfl⟩ := hy
  rw [← Units.val_mul, translateExtension_unit, translateExtension_unit]
  have h := ((mem_principalSeries_iff ℂ n _ φ).mp hφ).2 1 u (x * g)
  rw [map_one, one_mul] at h
  rw [mul_assoc, h]
  simp [principalSeriesCharacter, modulusCharacter]

theorem translateExtension_diagonal {φ : Langlands.GeneralLinear n ℂ → ℂ}
    (hφ : φ ∈ principalSeries ℂ n (modulusCharacter n)) (g : Langlands.GeneralLinear n ℂ)
    {y : Matrix (Fin n) (Fin n) ℂ} (hy : IsUnit y) (a : Fin n → ℂˣ) :
    translateExtension φ g (Matrix.diagonal (fun i => (a i : ℂ)) * y) =
      (∏ i : Fin n, ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) *
        ((‖(a i : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))) *
        translateExtension φ g y := by
  obtain ⟨x, rfl⟩ := hy
  have hd : Matrix.diagonal (fun i => (a i : ℂ)) * (x : Matrix (Fin n) (Fin n) ℂ) =
      ((Iwasawa.diagonalUnits a * x : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Units.val_mul, Iwasawa.diagonalUnits_val]
  rw [hd, translateExtension_unit, translateExtension_unit, ← modulus_mul_eq]
  have h := ((mem_principalSeries_iff ℂ n _ φ).mp hφ).2 a 1 (x * g)
  rw [Subgroup.coe_one, mul_one, ← mul_assoc] at h
  exact h

/-- The right derivative at `k y` of a modulus-equivariant function, as a derivative of the
translate by `y` along `k (y X y⁻¹)`. -/
theorem rightDerivative_eq_fderiv_translate {φ : Langlands.GeneralLinear n ℂ → ℂ}
    (hφ : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ φ) (k y : Langlands.GeneralLinear n ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    rightDerivative (matrixModel ℂ n) X φ (k * y) =
      fderiv ℝ (translateExtension φ y) (k : Matrix (Fin n) (Fin n) ℂ)
        ((k : Matrix (Fin n) (Fin n) ℂ) * ((y : Matrix (Fin n) (Fin n) ℂ) * X *
          ((y⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ))) := by
  rw [rightDerivative_eq_fderiv hφ]
  have hd : DifferentiableAt ℝ (unitsExtension φ)
      ((k : Matrix (Fin n) (Fin n) ℂ) * (y : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [← Units.val_mul]
    exact differentiableAt_unitsExtension hφ (Units.isUnit _)
  let R : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)).flip (y : Matrix (Fin n) (Fin n) ℂ)
  have hcomp : fderiv ℝ (translateExtension φ y) (k : Matrix (Fin n) (Fin n) ℂ) =
      (fderiv ℝ (unitsExtension φ) ((k : Matrix (Fin n) (Fin n) ℂ) *
        (y : Matrix (Fin n) (Fin n) ℂ))).comp R := by
    have h1 : HasFDerivAt (fun z : Matrix (Fin n) (Fin n) ℂ => z * (y : Matrix (Fin n) (Fin n) ℂ))
        R (k : Matrix (Fin n) (Fin n) ℂ) := R.hasFDerivAt
    exact (HasFDerivAt.comp (f := fun z : Matrix (Fin n) (Fin n) ℂ =>
      z * (y : Matrix (Fin n) (Fin n) ℂ)) (k : Matrix (Fin n) (Fin n) ℂ) hd.hasFDerivAt h1).fderiv
  rw [hcomp, ContinuousLinearMap.comp_apply, Units.val_mul]
  congr 1
  change (k : Matrix (Fin n) (Fin n) ℂ) * (y : Matrix (Fin n) (Fin n) ℂ) * X =
    (k : Matrix (Fin n) (Fin n) ℂ) * ((y : Matrix (Fin n) (Fin n) ℂ) * X *
      ((y⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) *
        (y : Matrix (Fin n) (Fin n) ℂ)
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  congr 2
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

/-! ## Integration along real diagonal one-parameter subgroups -/

open ComplexMatrixCoefficientAnalytic

/-- The `U(n)`-integral of `φ(k g)` is the `U(n)`-integral of `φ(k g exp(tH))`. -/
theorem integral_mul_expDiag_eq {φ : Langlands.GeneralLinear n ℂ → ℂ}
    (hφ : φ ∈ principalSeries ℂ n (modulusCharacter n)) (g : Langlands.GeneralLinear n ℂ)
    (h : Fin n → ℝ) (t : ℝ) :
    ∫ k, φ ((k : Langlands.GeneralLinear n ℂ) * g * expDiag h t) ∂unitaryHaar n =
      ∫ k, φ ((k : Langlands.GeneralLinear n ℂ) * g) ∂unitaryHaar n := by
  have hs := ((mem_principalSeries_iff ℂ n _ φ).mp hφ).1
  set H : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun j => (h j : ℂ)
  set ψ : ℝ → ℂ := fun t =>
    ∫ k, φ ((k : Langlands.GeneralLinear n ℂ) * g * expDiag h t) ∂unitaryHaar n
  have hR := contMDiff_rightDerivative hs H
  have hval : Continuous fun s : ℝ => ((expDiag h s : Langlands.GeneralLinear n ℂ) :
      Matrix (Fin n) (Fin n) ℂ) := by
    change Continuous fun s : ℝ => Matrix.diagonal fun j => ((Real.exp (s * h j) : ℝ) : ℂ)
    exact continuous_pi fun p => continuous_pi fun q => by
      simp only [Matrix.diagonal_apply]
      split_ifs
      · exact Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp (continuous_id.mul continuous_const))
      · exact continuous_const
  have hinv : ∀ s : ℝ, (expDiag h s)⁻¹ = expDiag h (-s) := fun s => by
    rw [inv_eq_of_mul_eq_one_right]
    rw [← expDiag_add, add_neg_cancel, expDiag_zero]
  have hexp : Continuous fun s : ℝ => expDiag h s := by
    rw [Units.continuous_iff]
    refine ⟨hval, ?_⟩
    simp_rw [hinv]
    exact hval.comp continuous_neg
  have hderiv : ∀ t₀ : ℝ, HasDerivAt ψ 0 t₀ := by
    intro t₀
    have hcontF : ∀ t : ℝ, Continuous fun k : unitaryCompact ℂ n =>
        φ ((k : Langlands.GeneralLinear n ℂ) * g * expDiag h t) := fun t =>
      hs.continuous.comp ((continuous_subtype_val.mul continuous_const).mul continuous_const)
    have hjoint : Continuous fun p : ℝ × unitaryCompact ℂ n =>
        rightDerivative (matrixModel ℂ n) H φ
          ((p.2 : Langlands.GeneralLinear n ℂ) * g * expDiag h p.1) :=
      hR.continuous.comp (((continuous_subtype_val.comp continuous_snd).mul continuous_const).mul
        (hexp.comp continuous_fst))
    obtain ⟨C, hC⟩ := ((isCompact_closedBall t₀ 1).prod isCompact_univ).exists_bound_of_continuousOn
      hjoint.continuousOn
    have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := unitaryHaar n)
      (F := fun t (k : unitaryCompact ℂ n) =>
        φ ((k : Langlands.GeneralLinear n ℂ) * g * expDiag h t))
      (F' := fun t (k : unitaryCompact ℂ n) => rightDerivative (matrixModel ℂ n) H φ
        ((k : Langlands.GeneralLinear n ℂ) * g * expDiag h t))
      (bound := fun _ => C) (ball_mem_nhds t₀ one_pos)
      (Filter.Eventually.of_forall fun t => (hcontF t).aestronglyMeasurable)
      (integrable_unitaryHaar (hcontF t₀))
      ((hjoint.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (ae_of_all _ fun k t ht => hC (t, k) ⟨ball_subset_closedBall ht, Set.mem_univ k⟩)
      (integrable_const C)
      (ae_of_all _ fun k t _ => hasDerivAt_mul_expDiag_at hs _ h t)
    have hzero : ∫ k, rightDerivative (matrixModel ℂ n) H φ
        ((k : Langlands.GeneralLinear n ℂ) * g * expDiag h t₀) ∂unitaryHaar n = 0 := by
      set y : Langlands.GeneralLinear n ℂ := g * expDiag h t₀
      have hpt : ∀ k : unitaryCompact ℂ n, rightDerivative (matrixModel ℂ n) H φ
          ((k : Langlands.GeneralLinear n ℂ) * g * expDiag h t₀) =
          fderiv ℝ (translateExtension φ y)
            ((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)
            (((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) *
              ((y : Matrix (Fin n) (Fin n) ℂ) * H *
                ((y⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ))) := fun k => by
        rw [mul_assoc]
        exact rightDerivative_eq_fderiv_translate hs _ y H
      rw [integral_congr_ae (ae_of_all _ hpt)]
      exact integral_fderiv_eq_zero (unitaryHaar n) (translateExtension_contDiffOn hs y)
        (fun z hz u => translateExtension_unipotent hφ y hz u)
        (fun z hz a => translateExtension_diagonal hφ y hz a) _
    rw [hzero] at hD
    exact hD.2
  have hconst := is_const_of_deriv_eq_zero (fun t => (hderiv t).differentiableAt)
    (fun t => (hderiv t).deriv) t 0
  simp only [ψ, expDiag_zero, mul_one] at hconst
  exact hconst

/-- **`GL_n(ℂ)`-invariance of the `U(n)`-integral.** -/
theorem integral_mul_eq {φ : Langlands.GeneralLinear n ℂ → ℂ}
    (hφ : φ ∈ principalSeries ℂ n (modulusCharacter n)) (g : Langlands.GeneralLinear n ℂ) :
    ∫ k, φ ((k : Langlands.GeneralLinear n ℂ) * g) ∂unitaryHaar n =
      ∫ k, φ (k : Langlands.GeneralLinear n ℂ) ∂unitaryHaar n := by
  obtain ⟨k₁, hk₁, k₂, hk₂, h, rfl⟩ := exists_kak g
  set φ₂ : Langlands.GeneralLinear n ℂ → ℂ := fun x => φ (x * k₂) with hφ₂
  have hφ₂m : φ₂ ∈ principalSeries ℂ n (modulusCharacter n) :=
    rightTranslation_mem_principalSeries (χ := modulusCharacter n) hφ k₂
  calc ∫ k, φ ((k : Langlands.GeneralLinear n ℂ) * (k₁ * expDiag h 1 * k₂)) ∂unitaryHaar n
      = ∫ k, φ₂ ((k : Langlands.GeneralLinear n ℂ) * k₁ * expDiag h 1) ∂unitaryHaar n := by
        refine integral_congr_ae (ae_of_all _ fun k => ?_)
        simp only [φ₂, mul_assoc]
    _ = ∫ k, φ₂ ((k : Langlands.GeneralLinear n ℂ) * k₁) ∂unitaryHaar n :=
        integral_mul_expDiag_eq hφ₂m k₁ h 1
    _ = ∫ k, φ₂ (k : Langlands.GeneralLinear n ℂ) ∂unitaryHaar n :=
        integral_mul_right_eq_self (μ := unitaryHaar n)
          (fun k : unitaryCompact ℂ n => φ₂ (k : Langlands.GeneralLinear n ℂ)) ⟨k₁, hk₁⟩
    _ = ∫ k, φ (k : Langlands.GeneralLinear n ℂ) ∂unitaryHaar n :=
        integral_mul_right_eq_self (μ := unitaryHaar n)
          (fun k : unitaryCompact ℂ n => φ (k : Langlands.GeneralLinear n ℂ)) ⟨k₂, hk₂⟩

end ComplexKIntegralInvariance

open ComplexKIntegralInvariance

/-- **Statement (`GL_n(ℂ)`-invariance of the `U(n)`-integral).** For every function `φ` in the
smooth principal series of `GL_n(ℂ)` of the characters `z ↦ (|z|²)^((n-1)/2 - i)` (the smooth
functions with `φ(diag(a) u g) = ∏ᵢ |aᵢ|^(2(n-1-2i)) φ(g)`: left equivariance under the upper
triangular Borel subgroup by its modulus character) and every `g ∈ GL_n(ℂ)`,
`∫_{U(n)} φ(k g) dk = ∫_{U(n)} φ(k) dk` for the Haar probability measure `unitaryHaar n`. -/
def ComplexKIntegralInvarianceStatement : Prop :=
  ∀ (n : ℕ) (φ : Langlands.GeneralLinear n ℂ → ℂ),
    φ ∈ principalSeries ℂ n (modulusCharacter n) →
      ∀ g : Langlands.GeneralLinear n ℂ,
        ∫ k, φ ((k : Langlands.GeneralLinear n ℂ) * g) ∂ComplexDuality.unitaryHaar n =
          ∫ k, φ (k : Langlands.GeneralLinear n ℂ) ∂ComplexDuality.unitaryHaar n

theorem complexKIntegralInvariance : ComplexKIntegralInvarianceStatement :=
  fun _ _ hφ g => integral_mul_eq hφ g

end Langlands.Archimedean
