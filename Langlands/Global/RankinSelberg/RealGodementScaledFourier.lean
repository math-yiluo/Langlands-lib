import Langlands.Global.RankinSelberg.RealGodementProductFourier
import Langlands.LocalFactor.ArchimedeanScaling

/-! # Complementary Fourier slices in real self-dual normalization -/

noncomputable section

open Langlands.LocalFactor.Archimedean
open Filter MeasureTheory
open scoped FourierTransform NNReal RealInnerProductSpace SchwartzMap

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

universe u v

/-- The measure scaling factor for the character of parameter `a`, one factor
`|a|^(1/2)` per real coordinate. -/
def euclideanHaarFactor (a : ℝˣ) (V : Type u) [AddCommGroup V] [Module ℝ V] : ℝ :=
  Real.sqrt |(a : ℝ)| ^ Module.finrank ℝ V

theorem euclideanHaarFactor_pos (a : ℝˣ) (V : Type u) [AddCommGroup V] [Module ℝ V] :
    0 < euclideanHaarFactor a V :=
  pow_pos (Real.sqrt_pos.mpr (abs_pos.mpr a.ne_zero)) _

theorem euclideanHaarFactor_mul_self (a : ℝˣ) (V : Type u) [AddCommGroup V] [Module ℝ V] :
    euclideanHaarFactor a V * euclideanHaarFactor a V = |(a : ℝ)| ^ Module.finrank ℝ V := by
  rw [euclideanHaarFactor, ← mul_pow, Real.mul_self_sqrt (abs_nonneg _)]

/-- Lebesgue measure rescaled for the real additive character of parameter `a`. -/
def euclideanSelfDualMeasure (a : ℝˣ) (V : Type u) [AddCommGroup V] [Module ℝ V]
    [MeasureSpace V] : Measure V := ENNReal.ofReal (euclideanHaarFactor a V) • volume

section Fourier

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

private def dilation (a : ℝˣ) : V ≃L[ℝ] V :=
  ({ toFun := fun x => (a : ℝ) • x
     invFun := fun x => (a : ℝ)⁻¹ • x
     left_inv x := by
       dsimp only
       rw [smul_smul, inv_mul_cancel₀ a.ne_zero, one_smul]
     right_inv x := by
       dsimp only
       rw [smul_smul, mul_inv_cancel₀ a.ne_zero, one_smul]
     map_add' x y := smul_add _ _ _
     map_smul' c x := smul_comm _ _ _ } : V ≃ₗ[ℝ] V).toContinuousLinearEquiv

/-- The positive Schwartz Fourier transform for the real additive character of
parameter `a` and its self-dual measure. -/
def scaledEuclideanFourier (a : ℝˣ) (Φ : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  (euclideanHaarFactor a V : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (dilation a)
    (𝓕⁻ Φ : 𝓢(V, ℂ))

theorem scaledEuclideanFourier_apply (a : ℝˣ) (Φ : 𝓢(V, ℂ)) (y : V) :
    scaledEuclideanFourier a Φ y =
      (euclideanHaarFactor a V : ℂ) * (𝓕⁻ Φ : 𝓢(V, ℂ)) ((a : ℝ) • y) := rfl

theorem scaledEuclideanFourier_eq_integral (a : ℝˣ) (Φ : 𝓢(V, ℂ)) (y : V) :
    scaledEuclideanFourier a Φ y =
      ∫ x : V, realScaledCharacter a (inner ℝ x y) • Φ x ∂euclideanSelfDualMeasure a V := by
  rw [scaledEuclideanFourier_apply, SchwartzMap.fourierInv_coe, Real.fourierInv_eq,
    euclideanSelfDualMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (euclideanHaarFactor_pos a V).le, Complex.real_smul]
  simp only [realScaledCharacter_apply, real_inner_smul_right]

end Fourier

section Product

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

local notation "P" => WithLp 2 (E × F)

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem euclideanHaarFactor_prod (a : ℝˣ) :
    euclideanHaarFactor a P = euclideanHaarFactor a E * euclideanHaarFactor a F := by
  simp only [euclideanHaarFactor, (WithLp.linearEquiv 2 ℝ (E × F)).finrank_eq,
    Module.finrank_prod, pow_add]

private theorem scaled_product_fourier (a : ℝˣ) (Φ : 𝓢(P, ℂ)) (ξ : E) (η : F) :
    Integrable (fun x : E => realScaledCharacter a (inner ℝ x ξ) • Φ (WithLp.toLp 2 (x, η)))
      (euclideanSelfDualMeasure a E) ∧
    Integrable (fun y : F => realScaledCharacter a (-(inner ℝ y η)) •
        scaledEuclideanFourier a Φ (WithLp.toLp 2 (ξ, y))) (euclideanSelfDualMeasure a F) ∧
    (∫ y : F, realScaledCharacter a (-(inner ℝ y η)) •
      scaledEuclideanFourier a Φ (WithLp.toLp 2 (ξ, y)) ∂euclideanSelfDualMeasure a F) =
    ∫ x : E, realScaledCharacter a (inner ℝ x ξ) • Φ (WithLp.toLp 2 (x, η))
      ∂euclideanSelfDualMeasure a E := by
  let L : E → ℂ := fun x => Real.fourierChar (inner ℝ x ((a : ℝ) • ξ)) • Φ (WithLp.toLp 2 (x, η))
  let R : F → ℂ := fun y => Real.fourierChar (-(inner ℝ y η)) •
    (𝓕⁻ Φ : 𝓢(P, ℂ)) (WithLp.toLp 2 ((a : ℝ) • ξ, y))
  have ⟨hL, hR, hEq⟩ : Integrable L ∧ Integrable R ∧ (∫ y, R y) = ∫ x, L x :=
    realGodementProductFourier E F Φ ((a : ℝ) • ξ) η
  have hLfun (x : E) : realScaledCharacter a (inner ℝ x ξ) • Φ (WithLp.toLp 2 (x, η)) = L x := by
    simp only [L, realScaledCharacter_apply, real_inner_smul_right]
  have hRfun (y : F) : realScaledCharacter a (-(inner ℝ y η)) •
      scaledEuclideanFourier a Φ (WithLp.toLp 2 (ξ, y)) =
      (euclideanHaarFactor a P : ℂ) * R ((a : ℝ) • y) := by
    simp only [R, scaledEuclideanFourier_apply, ← WithLp.toLp_smul, Prod.smul_mk,
      realScaledCharacter_apply, real_inner_smul_left, mul_neg, Circle.smul_def, smul_eq_mul]
    ring
  have hC₁ := euclideanHaarFactor_pos a E
  have hC₂ := euclideanHaarFactor_pos a F
  constructor
  · simp only [hLfun, euclideanSelfDualMeasure]
    exact (integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr hC₁) ENNReal.ofReal_ne_top).mpr hL
  constructor
  · simp only [hRfun, euclideanSelfDualMeasure]
    exact (integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr hC₂) ENNReal.ofReal_ne_top).mpr
      ((hR.comp_smul a.ne_zero).const_mul _)
  · simp only [hLfun, hRfun, euclideanSelfDualMeasure, integral_smul_measure,
      ENNReal.toReal_ofReal hC₁.le, ENNReal.toReal_ofReal hC₂.le, integral_const_mul]
    rw [Measure.integral_comp_smul volume R (a : ℝ), abs_inv, abs_pow, hEq,
      euclideanHaarFactor_prod, Complex.ofReal_mul]
    simp only [Complex.real_smul, Complex.ofReal_inv]
    rw [← euclideanHaarFactor_mul_self a F, Complex.ofReal_mul]
    field_simp [Complex.ofReal_ne_zero.mpr hC₂.ne']

end Product

/-- Complementary real product slices use the exact positive Fourier transform
and self-dual measure for the scaled additive character. -/
def RealGodementScaledProductFourierStatement : Prop :=
  ∀ (E : Type u) (F : Type v)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (a : ℝˣ) (Φ : 𝓢(WithLp 2 (E × F), ℂ)) (ξ : E) (η : F),
    Integrable (fun x : E => realScaledCharacter a (inner ℝ x ξ) • Φ (WithLp.toLp 2 (x, η)))
      (euclideanSelfDualMeasure a E) ∧
    Integrable (fun y : F => realScaledCharacter a (-(inner ℝ y η)) •
        scaledEuclideanFourier a Φ (WithLp.toLp 2 (ξ, y))) (euclideanSelfDualMeasure a F) ∧
    (∫ y : F, realScaledCharacter a (-(inner ℝ y η)) •
      scaledEuclideanFourier a Φ (WithLp.toLp 2 (ξ, y)) ∂euclideanSelfDualMeasure a F) =
    ∫ x : E, realScaledCharacter a (inner ℝ x ξ) • Φ (WithLp.toLp 2 (x, η))
      ∂euclideanSelfDualMeasure a E

theorem realGodementScaledProductFourier : RealGodementScaledProductFourierStatement.{u, v} := by
  intro E F _ _ _ _ _ _ _ _ _ _ a Φ ξ η
  exact scaled_product_fourier a Φ ξ η

end Langlands.Global.RankinSelbergGlobal.RealGodement
