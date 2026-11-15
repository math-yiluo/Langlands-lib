import Langlands.Representation.Archimedean.JacquetDual
import Langlands.Representation.Archimedean.TranslateFinite
import Langlands.Representation.Archimedean.PrincipalSeriesAnnihilator

/-!
# Proper submodules of strictly dominant principal series lie in the kernel of the Jacquet
integral
-/

noncomputable section

open MeasureTheory Matrix ComplexConjugate

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace JacquetKernel

open MaximalParabolicIntegration ParabolicChartBound PartialJacquet JacquetLimit JacquetDual
  GramFormula Langlands.GeneralLinear RealPrincipalSeriesDuality PrincipalSeriesExtension
  TranslateFinite

attribute [local instance] measurableSpaceK

local instance borelSpaceK_jk (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

/-! ## Linearity of the Jacquet integral -/

theorem jacquetStep_smul {m : ℕ} (c : ℂ) (h : Langlands.GeneralLinear (m + 1) ℝ → ℂ) :
    jacquetStep (c • h) = c • jacquetStep h := by
  funext g
  simp only [jacquetStep, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

theorem jacquet_smul : ∀ (n : ℕ) (c : ℂ) (h : Langlands.GeneralLinear n ℝ → ℂ),
    jacquet n (c • h) = c * jacquet n h
  | 0, _, _ => rfl
  | m + 1, c, h => by
      change jacquet m (jacquetStep (c • h)) = c * jacquet m (jacquetStep h)
      rw [jacquetStep_smul]
      exact jacquet_smul m c _

theorem jacquetStep_add {m : ℕ} (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e m)
    {h₁ h₂ : Langlands.GeneralLinear (m + 1) ℝ → ℂ} (hh₁ : h₁ ∈ principalSeries ℝ (m + 1) χ)
    (hh₂ : h₂ ∈ principalSeries ℝ (m + 1) χ) :
    jacquetStep (h₁ + h₂) = jacquetStep h₁ + jacquetStep h₂ := by
  funext g
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  rw [Pi.add_apply, jacquetStep_mul (add_mem hh₁ hh₂) (hχ.one m), jacquetStep_mul hh₁ (hχ.one m),
    jacquetStep_mul hh₂ (hχ.one m), ← mul_add]
  congr 1
  have hκ := iotaGL_mem_unitaryCompact hk
  exact integral_add (integrable_chart hχ he hh₁ hκ) (integrable_chart hχ he hh₂ hκ)

theorem jacquet_add : ∀ (n : ℕ) {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}, IsSignedPower χ e →
    IsStrictlyDominant e (n - 1) → ∀ {h₁ h₂ : Langlands.GeneralLinear n ℝ → ℂ},
    h₁ ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) →
    h₂ ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) →
    jacquet n (h₁ + h₂) = jacquet n h₁ + jacquet n h₂
  | 0, _, _, _, _, _, _, _, _ => rfl
  | m + 1, χ, e, hχ, he, h₁, h₂, hh₁, hh₂ => by
      have he' : IsStrictlyDominant e m := by simpa using he
      change jacquet m (jacquetStep (h₁ + h₂)) =
        jacquet m (jacquetStep h₁) + jacquet m (jacquetStep h₂)
      rw [jacquetStep_add hχ he' hh₁.1 hh₂.1]
      exact jacquet_add m hχ.shift (isStrictlyDominant_shift he') (jacquetStep_mem hχ he' hh₁)
        (jacquetStep_mem hχ he' hh₂)

/-- The `O(n)`-finite functions of the principal series on which the Jacquet integral
vanishes. -/
def jacquetKernel (n : ℕ) (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e (n - 1)) :
    Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) where
  carrier := {f | f ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) ∧
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

theorem continuous_of_mem {χ' : ℕ → ℝˣ → ℂ} {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℝ n χ') (unitaryCompact ℝ n)) : Continuous f :=
  hf.1.1.continuous

/-- The annihilator of `W` in the `O(n)`-finite functions of the dual principal series. -/
def annihilator (χ : ℕ → ℝˣ → ℂ) (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
    (hW : W ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)) :
    Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) where
  carrier := {u | u ∈ kFiniteFunctions (principalSeries ℝ n (dualChar χ)) (unitaryCompact ℝ n) ∧
    ∀ w ∈ W, ∫ k, u (k : Langlands.GeneralLinear n ℝ) * w k ∂haarK n = 0}
  zero_mem' := ⟨Submodule.zero_mem _, fun w _ => by simp⟩
  add_mem' {u v} hu hv := ⟨add_mem hu.1 hv.1, fun w hw => by
    simp only [Pi.add_apply, add_mul]
    rw [integral_add (integrable_mul_of_continuous (continuous_of_mem hu.1)
      (continuous_of_mem (hW hw))) (integrable_mul_of_continuous (continuous_of_mem hv.1)
      (continuous_of_mem (hW hw))), hu.2 w hw, hv.2 w hw, add_zero]⟩
  smul_mem' c u hu := ⟨Submodule.smul_mem _ c hu.1, fun w hw => by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, hu.2 w hw, mul_zero]⟩

theorem annihilator_le (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
    (hW : W ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)) :
    annihilator χ W hW ≤ kFiniteFunctions (principalSeries ℝ n (dualChar χ)) (unitaryCompact ℝ n) :=
  fun _ hu => hu.1

theorem annihilator_rightTranslation (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
    (hW : W ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n))
    (hWK : ∀ k ∈ unitaryCompact ℝ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k w ∈ W) :
    ∀ k ∈ unitaryCompact ℝ n, ∀ u ∈ annihilator χ W hW,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k u ∈ annihilator χ W hW := by
  intro k hk u hu
  refine ⟨rightTranslation_mem_kFiniteFunctions_principalSeries (χ := dualChar χ)
    (unitaryCompact ℝ n) hu.1 hk, fun w hw => ?_⟩
  have hw' := hu.2 _ (hWK _ (inv_mem hk) w hw)
  rw [← integral_mul_right_eq_self (μ := haarK n) _ (⟨k, hk⟩ : unitaryCompact ℝ n)] at hw'
  refine (integral_congr_ae (ae_of_all _ fun κ => ?_)).trans hw'
  change u ((κ : Langlands.GeneralLinear n ℝ) * k) * w κ =
    u ((κ : Langlands.GeneralLinear n ℝ) * k) * w ((κ : Langlands.GeneralLinear n ℝ) * k * k⁻¹)
  rw [mul_inv_cancel_right]

theorem annihilator_rightDerivative (hχ : IsSignedPower χ e)
    (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
    (hW : W ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n))
    (hWD : ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ w ∈ W, rightDerivative (matrixModel ℝ n) X w ∈ W) :
    ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ u ∈ annihilator χ W hW,
      rightDerivative (matrixModel ℝ n) X u ∈ annihilator χ W hW := by
  intro X u hu
  refine ⟨rightDerivative_mem_kFiniteFunctions_principalSeries (χ := dualChar χ)
    (unitaryCompact ℝ n) hu.1 X, fun w hw => ?_⟩
  have hwX := hW hw
  have hinv : ∀ (i : ℕ) (x : ℝˣ), dualChar χ i x * χ i x = 1 := fun i x =>
    inv_mul_cancel₀ (hχ.ne_zero i x)
  have h0 := integral_rightDerivative_eq_zero (contMDiff_mul_fun hu.1.1.1 hwX.1.1)
    (isModulusEquivariant_mul hinv hu.1.1 hwX.1) X
  simp only [rightDerivative_mul_fun hu.1.1.1 hwX.1.1] at h0
  have hDu := rightDerivative_mem_kFiniteFunctions_principalSeries (χ := dualChar χ)
    (unitaryCompact ℝ n) hu.1 X
  have hDw := rightDerivative_mem_kFiniteFunctions_principalSeries (χ := χ)
    (unitaryCompact ℝ n) hwX X
  rw [integral_add (integrable_mul_of_continuous (continuous_of_mem hDu) (continuous_of_mem hwX))
    (integrable_mul_of_continuous (continuous_of_mem hu.1) (continuous_of_mem hDw)),
    hu.2 _ (hWD X w hw), add_zero] at h0
  exact h0

theorem conj_eval_ofReal {σ : Type*} (P : MvPolynomial σ ℂ) (x : σ → ℝ) :
    conj (MvPolynomial.eval (fun i => (x i : ℂ)) P) =
      MvPolynomial.eval (fun i => (x i : ℂ)) (MvPolynomial.map (starRingEnd ℂ) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem conj_eq_inv_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : conj z = z⁻¹ := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact zero_ne_one hz
  have h : conj z * z = 1 := by
    rw [RCLike.conj_mul, hz]
    simp
  exact eq_inv_of_mul_eq_one_left h

theorem principalSeriesCharacter_sign (N : ℕ) (a : Fin N → ℝˣ) :
    principalSeriesCharacter ℝ N χ (fun i => signUnit (a i)) =
      ∏ i : Fin N, χ i (signUnit (a i)) := by
  rw [principalSeriesCharacter]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Module.finrank_self, pow_one, Real.norm_eq_abs, GramFormula.abs_signUnit,
    Complex.ofReal_one, Complex.one_cpow, mul_one]

theorem annihilator_ne_bot (hχ : IsSignedPower χ e)
    (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
    (hW : W ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n))
    (hWK : ∀ k ∈ unitaryCompact ℝ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k w ∈ W)
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)) (hfW : f ∉ W) :
    annihilator χ W hW ≠ ⊥ := by
  obtain ⟨v, hv, ⟨k₀, hk₀⟩, hvW⟩ := PrincipalSeriesAnnihilator.exists_orthogonal W hW hWK hf hfW
  obtain ⟨P, hP⟩ := OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors
    (continuous_of_mem hv) hv.2 1
  set φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ := fun κ => conj (v (Unitary.toUnits κ)) with hφdef
  have hφP : ∀ κ : Matrix.unitaryGroup (Fin n) ℝ, φ κ = MvPolynomial.eval
      (fun ij => (((κ : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℝ) : ℂ))
        (MvPolynomial.map (starRingEnd ℂ) P) := by
    intro κ
    rw [hφdef]
    simp only
    rw [← one_mul (Unitary.toUnits κ), hP κ]
    exact conj_eval_ofReal P (fun ij => (κ : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2)
  have hφc : Continuous φ :=
    Complex.continuous_conj.comp ((continuous_of_mem hv).comp continuous_unitary_toUnits)
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => φ (x * k))) := by
    have h := finiteDimensional_span_eval (n := n) (MvPolynomial.map (starRingEnd ℂ) P)
    have heq : (fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => φ (x * k)) =
        fun k x => MvPolynomial.eval (fun ij => (((x * k : Matrix.unitaryGroup (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℂ)) (MvPolynomial.map (starRingEnd ℂ) P) :=
      funext fun k => funext fun x => hφP (x * k)
    rw [heq]
    exact h
  have hφM : ∀ (a : Fin n → ℝˣ) (κ : Matrix.unitaryGroup (Fin n) ℝ),
      φ (signDiagonal (fun i => (a i : ℝ)) * κ) =
        principalSeriesCharacter ℝ n (dualChar χ) (fun i => signUnit (a i)) * φ κ := by
    intro a κ
    simp only [hφdef]
    rw [signDiagonal_toUnits, hv.1.2, map_mul, principalSeriesCharacter_sign,
      principalSeriesCharacter_sign, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [dualChar, conj_eq_inv_of_norm_eq_one (hχ.norm_sign i (a i))]
  have hE := extension_mem_kFiniteFunctions (fun l => -e l) hχ.dual.eq hφc hfin hφM
  set u := extension (shiftedExponent n (fun l => -e l)) φ with hudef
  have hu_val : ∀ k : unitaryCompact ℝ n, u k = conj (v k) := by
    intro k
    have hk : (k : Langlands.GeneralLinear n ℝ) = Unitary.toUnits (toUnitaryGroup n k) :=
      Units.ext rfl
    rw [hudef, hk, extension_unitary, hφdef]
  have hmem : u ∈ annihilator χ W hW := ⟨hE, fun w hw => by
    simp only [hu_val]
    rw [← hvW w hw]
    exact integral_congr_ae (ae_of_all _ fun k => mul_comm _ _)⟩
  intro hbot
  rw [hbot, Submodule.mem_bot] at hmem
  have := congrFun hmem k₀
  rw [hu_val, Pi.zero_apply, map_eq_zero] at this
  exact hk₀ this

/-! ## Proper submodules -/

/-- **Proper submodules lie in the kernel of the Jacquet integral.** -/
theorem jacquet_eq_zero_of_proper (hχ : IsSignedPower χ e) (he : IsStrictlyDominant e (n - 1))
    (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
    (hW : W ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n))
    (hWK : ∀ k ∈ unitaryCompact ℝ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k w ∈ W)
    (hWD : ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ w ∈ W, rightDerivative (matrixModel ℝ n) X w ∈ W)
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)) (hfW : f ∉ W) :
    W ≤ jacquetKernel n hχ he := fun w hw =>
  ⟨hW hw, jacquet_eq_zero n hχ he (annihilator_le W hW) (annihilator_rightTranslation W hW hWK)
    (annihilator_rightDerivative hχ W hW hWD) (annihilator_ne_bot hχ W hW hWK hf hfW) (hW hw)
    fun _ hu => hu.2 w hw⟩

end JacquetKernel

end Langlands.Archimedean
