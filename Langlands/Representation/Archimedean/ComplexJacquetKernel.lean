import Langlands.Representation.Archimedean.ComplexJacquetDual
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesAnnihilator
import Langlands.Representation.Archimedean.ComplexDuality.Pairing

/-!
# Proper submodules of strictly dominant complex principal series lie in the kernel of the
Jacquet integral

For strictly dominant phase-power characters `χ` of `GL_n(ℂ)`, every proper
`(𝔤, K)`-stable subspace of the `U(n)`-finite principal series of `χ` lies in the kernel of the
Jacquet integral `Λ_n` (`ComplexJacquetKernel.jacquet_eq_zero_of_proper`).
-/

noncomputable section

open MeasureTheory Matrix ComplexConjugate

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexJacquetKernel

open ComplexMaximalParabolicIntegration ComplexParabolicChartBound ComplexPartialJacquet
  ComplexJacquetLimit ComplexJacquetDual ComplexGramFormula Langlands.GeneralLinear
  ComplexDuality ComplexPrincipalSeriesAnnihilator

variable {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-! ## Linearity of the Jacquet integral -/

theorem jacquetStep_smul {m : ℕ} (c : ℂ) (h : Langlands.GeneralLinear (m + 1) ℂ → ℂ) :
    jacquetStep (c • h) = c • jacquetStep h := by
  funext g
  simp only [jacquetStep, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

theorem jacquet_smul : ∀ (n : ℕ) (c : ℂ) (h : Langlands.GeneralLinear n ℂ → ℂ),
    jacquet n (c • h) = c * jacquet n h
  | 0, _, _ => rfl
  | m + 1, c, h => by
      change jacquet m (jacquetStep (c • h)) = c * jacquet m (jacquetStep h)
      rw [jacquetStep_smul]
      exact jacquet_smul m c _

theorem jacquetStep_add {m : ℕ} (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e m)
    {h₁ h₂ : Langlands.GeneralLinear (m + 1) ℂ → ℂ} (hh₁ : h₁ ∈ principalSeries ℂ (m + 1) χ)
    (hh₂ : h₂ ∈ principalSeries ℂ (m + 1) χ) :
    jacquetStep (h₁ + h₂) = jacquetStep h₁ + jacquetStep h₂ := by
  funext g
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  rw [Pi.add_apply, jacquetStep_mul (add_mem hh₁ hh₂) (hχ.one m), jacquetStep_mul hh₁ (hχ.one m),
    jacquetStep_mul hh₂ (hχ.one m), ← mul_add]
  congr 1
  have hκ := iotaGL_mem_unitaryCompact hk
  exact integral_add (integrable_chart hχ he hh₁ hκ) (integrable_chart hχ he hh₂ hκ)

theorem jacquet_add : ∀ (n : ℕ) {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}, IsPhasePower χ e →
    IsStrictlyDominant e (n - 1) → ∀ {h₁ h₂ : Langlands.GeneralLinear n ℂ → ℂ},
    h₁ ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) →
    h₂ ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) →
    jacquet n (h₁ + h₂) = jacquet n h₁ + jacquet n h₂
  | 0, _, _, _, _, _, _, _, _ => rfl
  | m + 1, χ, e, hχ, he, h₁, h₂, hh₁, hh₂ => by
      have he' : IsStrictlyDominant e m := by simpa using he
      change jacquet m (jacquetStep (h₁ + h₂)) =
        jacquet m (jacquetStep h₁) + jacquet m (jacquetStep h₂)
      rw [jacquetStep_add hχ he' hh₁.1 hh₂.1]
      exact jacquet_add m hχ.shift (isStrictlyDominant_shift he') (jacquetStep_mem hχ he' hh₁)
        (jacquetStep_mem hχ he' hh₂)

/-- The `U(n)`-finite functions of the principal series on which the Jacquet integral
vanishes. -/
def jacquetKernel (n : ℕ) (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e (n - 1)) :
    Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) where
  carrier := {f | f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) ∧
    jacquet n f = 0}
  zero_mem' := ⟨Submodule.zero_mem _, by
    have := jacquet_smul n 0 0
    rwa [zero_smul, zero_mul] at this⟩
  add_mem' {f g} hf hg := ⟨add_mem hf.1 hg.1, by
    rw [jacquet_add n hχ he hf.1 hg.1, hf.2, hg.2, add_zero]⟩
  smul_mem' c f hf := ⟨Submodule.smul_mem _ c hf.1, by
    rw [jacquet_smul, hf.2, mul_zero]⟩

/-! ## The annihilator -/

variable {n : ℕ}

/-- The annihilator of `W` in the `U(n)`-finite functions of the dual principal series. -/
def annihilator (χ : ℕ → ℂˣ → ℂ) (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ))
    (hW : W ≤ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) :
    Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) where
  carrier := {u | u ∈ kFiniteFunctions (principalSeries ℂ n (dualChar χ)) (unitaryCompact ℂ n) ∧
    ∀ w ∈ W, ∫ k, u (k : Langlands.GeneralLinear n ℂ) * w k ∂unitaryHaar n = 0}
  zero_mem' := ⟨Submodule.zero_mem _, fun w _ => by simp⟩
  add_mem' {u v} hu hv := ⟨add_mem hu.1 hv.1, fun w hw => by
    simp only [Pi.add_apply, add_mul]
    rw [integral_add (integrable_mul_of_continuous (continuous_of_mem_kFiniteFunctions hu.1)
      (continuous_of_mem_kFiniteFunctions (hW hw)))
      (integrable_mul_of_continuous (continuous_of_mem_kFiniteFunctions hv.1)
      (continuous_of_mem_kFiniteFunctions (hW hw))), hu.2 w hw, hv.2 w hw, add_zero]⟩
  smul_mem' c u hu := ⟨Submodule.smul_mem _ c hu.1, fun w hw => by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, hu.2 w hw, mul_zero]⟩

theorem annihilator_le (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ))
    (hW : W ≤ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) :
    annihilator χ W hW ≤ kFiniteFunctions (principalSeries ℂ n (dualChar χ)) (unitaryCompact ℂ n) :=
  fun _ hu => hu.1

theorem annihilator_rightTranslation (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ))
    (hW : W ≤ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    (hWK : ∀ k ∈ unitaryCompact ℂ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k w ∈ W) :
    ∀ k ∈ unitaryCompact ℂ n, ∀ u ∈ annihilator χ W hW,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k u ∈ annihilator χ W hW := by
  intro k hk u hu
  refine ⟨rightTranslation_mem_kFiniteFunctions_principalSeries (χ := dualChar χ)
    (unitaryCompact ℂ n) hu.1 hk, fun w hw => ?_⟩
  have hw' := hu.2 _ (hWK _ (inv_mem hk) w hw)
  rw [← integral_mul_right_eq_self (μ := unitaryHaar n) _ (⟨k, hk⟩ : unitaryCompact ℂ n)] at hw'
  refine (integral_congr_ae (ae_of_all _ fun κ => ?_)).trans hw'
  change u ((κ : Langlands.GeneralLinear n ℂ) * k) * w κ =
    u ((κ : Langlands.GeneralLinear n ℂ) * k) * w ((κ : Langlands.GeneralLinear n ℂ) * k * k⁻¹)
  rw [mul_inv_cancel_right]

theorem annihilator_rightDerivative (hχ : IsPhasePower χ e)
    (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ))
    (hW : W ≤ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    (hWD : ∀ (X : Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, rightDerivative (matrixModel ℂ n) X w ∈ W) :
    ∀ (X : Matrix (Fin n) (Fin n) ℂ), ∀ u ∈ annihilator χ W hW,
      rightDerivative (matrixModel ℂ n) X u ∈ annihilator χ W hW := by
  intro X u hu
  refine ⟨rightDerivative_mem_kFiniteFunctions_principalSeries (χ := dualChar χ)
    (unitaryCompact ℂ n) hu.1 X, fun w hw => ?_⟩
  have hwX := hW hw
  have hinv : ∀ (i : ℕ) (z : ℂˣ), dualChar χ i z * χ i z = 1 := fun i z =>
    inv_mul_cancel₀ (hχ.ne_zero i z)
  have h0 := integral_rightDerivative_mul_add_eq_zero (unitaryHaar n) (dualChar χ) χ hinv
    hu.1.1 hwX.1 X
  rw [hu.2 _ (hWD X w hw), add_zero] at h0
  exact h0

theorem normSq_dualChar (hχ : IsPhasePower χ e) (i : ℕ) (z : ℂˣ) :
    Complex.normSq (dualChar χ i z) = Complex.normSq (z : ℂ) ^ (-(2 * (e i).re)) := by
  have hz : 0 ≤ ‖(z : ℂ)‖ := norm_nonneg _
  rw [dualChar, map_inv₀, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hχ.norm]
  simp only [← Real.rpow_natCast]
  rw [← Real.rpow_mul hz, ← Real.rpow_mul hz, ← Real.rpow_neg hz]
  congr 1
  push_cast
  ring

theorem annihilator_ne_bot (hχ : IsPhasePower χ e)
    (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ))
    (hW : W ≤ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    (hWK : ∀ k ∈ unitaryCompact ℂ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k w ∈ W)
    {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) (hfW : f ∉ W) :
    annihilator χ W hW ≠ ⊥ := by
  have hinv : ∀ (i : ℕ) (z : ℂˣ), dualChar χ i z * χ i z = 1 := fun i z =>
    inv_mul_cancel₀ (hχ.ne_zero i z)
  obtain ⟨u, hu, ⟨k₀, hk₀⟩, huW⟩ := exists_dual_annihilator hinv (normSq_dualChar hχ) W hW hWK
    hf hfW
  have hmem : u ∈ annihilator χ W hW := ⟨hu, fun w hw => by
    rw [← huW w hw]
    exact integral_congr_ae (ae_of_all _ fun k => mul_comm _ _)⟩
  intro hbot
  rw [hbot, Submodule.mem_bot] at hmem
  exact hk₀ (congrFun hmem k₀)

/-! ## Proper submodules -/

/-- **Proper submodules lie in the kernel of the Jacquet integral.** -/
theorem jacquet_eq_zero_of_proper (hχ : IsPhasePower χ e) (he : IsStrictlyDominant e (n - 1))
    (W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ))
    (hW : W ≤ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    (hWK : ∀ k ∈ unitaryCompact ℂ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k w ∈ W)
    (hWD : ∀ (X : Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, rightDerivative (matrixModel ℂ n) X w ∈ W)
    {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) (hfW : f ∉ W) :
    W ≤ jacquetKernel n hχ he := fun w hw =>
  ⟨hW hw, jacquet_eq_zero n hχ he (annihilator_le W hW) (annihilator_rightTranslation W hW hWK)
    (annihilator_rightDerivative hχ W hW hWD) (annihilator_ne_bot hχ W hW hWK hf hfW) (hW hw)
    fun _ hu => hu.2 w hw⟩

end ComplexJacquetKernel

/-- **Proper submodules of strictly dominant complex principal series lie in the kernel of the
Jacquet integral.** Let `χ_0, …, χ_{n-1}` be characters of `ℂˣ` with
`χ_l(z) = χ_l(z/|z|) (|z|²)^{e_l}`, `χ_l(1) = 1`, `|χ_l| = 1` on the unit circle and
`Re e_0 > ⋯ > Re e_{n-1}`. Let `W` be a subspace of the `U(n)`-finite functions of the smooth
principal series of `χ`, stable under right translation by `U(n)` and under right derivatives
along all `X ∈ 𝔤𝔩_n(ℂ)`, and proper: some `U(n)`-finite function `f` of the principal series is
not in `W`. Then the Jacquet integral `Λ_n` (`ComplexJacquetDual.jacquet`) vanishes on `W`. -/
def ComplexJacquetKernelStatement : Prop :=
  ∀ (n : ℕ) (χ : ℕ → ℂˣ → ℂ) (e : ℕ → ℂ),
    (∀ (l : ℕ) (z : ℂˣ), χ l z =
      χ l (ComplexGramFormula.phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l) →
    (∀ l : ℕ, χ l 1 = 1) →
    (∀ (l : ℕ) (z : ℂˣ), ‖χ l (ComplexGramFormula.phaseUnit z)‖ = 1) →
    (∀ l : ℕ, l + 1 < n → (e (l + 1)).re < (e l).re) →
    ∀ W : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ),
    W ≤ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) →
    (∀ k ∈ unitaryCompact ℂ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k w ∈ W) →
    (∀ (X : Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, rightDerivative (matrixModel ℂ n) X w ∈ W) →
    (∃ f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n), f ∉ W) →
    ∀ w ∈ W, ComplexJacquetDual.jacquet n w = 0

theorem complexJacquetKernel : ComplexJacquetKernelStatement := by
  intro n χ e heq hone hphase hdom W hW hWK hWD ⟨f, hf, hfW⟩ w hw
  have hχ : ComplexPartialJacquet.IsPhasePower χ e := ⟨heq, hone, hphase⟩
  exact (ComplexJacquetKernel.jacquet_eq_zero_of_proper hχ (fun l hl => hdom l (by omega)) W hW
    hWK hWD hf hfW hw).2

end Langlands.Archimedean
