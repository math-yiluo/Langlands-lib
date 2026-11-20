import Langlands.Analysis.SchwartzMarginal
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Fourier transformation of slices and marginals -/

noncomputable section

open MeasureTheory WithLp
open scoped FourierTransform RealInnerProductSpace SchwartzMap

namespace Langlands.Analysis.SchwartzFourierMarginal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section TwoFactors

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "P" => WithLp 2 (E × F)

private abbrev coordinates : P ≃L[ℝ] (E × F) := WithLp.prodContinuousLinearEquiv 2 ℝ E F

private def inclusion : E →L[ℝ] P :=
  (coordinates (E := E) (F := F)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E F)

private theorem isometry_inclusion : Isometry (inclusion (E := E) (F := F)) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact WithLp.norm_toLp_fst 2 E F (x - y)

/-- Evaluate a Schwartz function on the first factor at second coordinate zero. -/
def zeroSlice (Φ : 𝓢(P, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ inclusion.hasTemperateGrowth isometry_inclusion.antilipschitzWith Φ

@[simp] theorem zeroSlice_apply (Φ : 𝓢(P, ℂ)) (x : E) : zeroSlice Φ x = Φ (toLp 2 (x, 0)) := rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- Integrate a Schwartz function over the second factor. -/
def marginal (Φ : 𝓢(P, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMarginal.marginalCLM (volume : Measure F)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coordinates.symm Φ)

@[simp] theorem marginal_apply (Φ : 𝓢(P, ℂ)) (x : E) :
    marginal Φ x = ∫ y : F, Φ (toLp 2 (x, y)) := by
  simp [marginal]

variable [MeasurableSpace E] [BorelSpace E]

/-- The Fourier transform of a marginal is the corresponding zero slice of the Fourier transform. -/
theorem fourier_marginal (Φ : 𝓢(P, ℂ)) : 𝓕 (marginal Φ) = zeroSlice (𝓕 Φ) := by
  ext x
  rw [SchwartzMap.fourier_coe, zeroSlice_apply, SchwartzMap.fourier_coe, Real.fourier_eq, Real.fourier_eq]
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (coordinates (E := E) (F := F)).symm Φ
  let K : P → ℂ := fun p => Real.fourierChar (-inner ℝ p (toLp 2 (x, 0))) • Φ p
  let A : E × F → ℂ := fun p => Real.fourierChar (-inner ℝ p.1 x) • g p
  have hA : Integrable A ((volume : Measure E).prod (volume : Measure F)) := by
    have hg : Integrable (g : E × F → ℂ) ((volume : Measure E).prod (volume : Measure F)) := g.integrable
    refine hg.norm.mono' ?_ (ae_of_all _ fun p => ?_)
    · exact ((Real.continuous_fourierChar.comp ((continuous_fst.inner continuous_const).neg)).smul
        g.continuous).aestronglyMeasurable
    · change ‖Real.fourierChar (-inner ℝ p.1 x) • g p‖ ≤ ‖g p‖
      rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
  have hK (p : E × F) : K (toLp 2 p) = A p := by
    simp [K, A, g, WithLp.prod_inner_apply]
  calc
    (∫ u : E, Real.fourierChar (-inner ℝ u x) • marginal Φ u) =
        ∫ p : E × F, A p := by
      rw [Measure.volume_eq_prod E F, integral_prod _ hA]
      apply integral_congr_ae
      filter_upwards with u
      simp only [marginal_apply, A, g, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
      simp only [Circle.smul_def, ← integral_smul]
      rfl
    _ = ∫ p : E × F, K (toLp 2 p) := by simp only [hK]
    _ = ∫ p, K p := (WithLp.volume_preserving_toLp E F).integral_comp'
      (f := MeasurableEquiv.toLp 2 (E × F)) K

/-- Integration of the Fourier transform equals Fourier transformation of the zero slice. -/
theorem marginal_fourier (Φ : 𝓢(P, ℂ)) : marginal (𝓕 Φ) = 𝓕 (zeroSlice Φ) := by
  have h (Ψ : 𝓢(P, ℂ)) : 𝓕⁻ (marginal Ψ) = zeroSlice (𝓕⁻ Ψ) := by
    ext x
    have hp := congrArg (fun f : 𝓢(E, ℂ) => f (-x)) (fourier_marginal Ψ)
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, zeroSlice_apply,
      SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
    simpa only [zeroSlice_apply, SchwartzMap.fourier_coe, ← toLp_neg, Prod.neg_mk, neg_zero] using hp
  have hΦ := h (𝓕 Φ)
  rw [FourierTransform.fourierInv_fourier_eq] at hΦ
  have hs := congrArg (fun f : 𝓢(E, ℂ) => 𝓕 f) hΦ
  rwa [FourierTransform.fourier_fourierInv_eq] at hs

end TwoFactors

section ThreeFactors

variable {E U L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [NormedAddCommGroup L] [InnerProductSpace ℝ L]

local notation "Q" => WithLp 2 (E × L)
local notation "P" => WithLp 2 (E × WithLp 2 (U × L))

private def swapMiddleLinear : WithLp 2 (Q × U) ≃ₗ[ℝ] P where
  toFun p := toLp 2 ((ofLp (ofLp p).1).1, toLp 2 ((ofLp p).2, (ofLp (ofLp p).1).2))
  invFun p := toLp 2 (toLp 2 ((ofLp p).1, (ofLp (ofLp p).2).2), (ofLp (ofLp p).2).1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def swapMiddle : WithLp 2 (Q × U) ≃ₗᵢ[ℝ] P :=
  swapMiddleLinear.isometryOfInner fun p q => by
    simp [WithLp.prod_inner_apply, swapMiddleLinear, add_comm, add_assoc]

private theorem swapMiddle_apply (x : E) (y : U) (z : L) :
    swapMiddle (toLp 2 (toLp 2 (x, z), y)) = (toLp 2 (x, toLp 2 (y, z)) : P) := rfl

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ U] [FiniteDimensional ℝ L]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace U] [BorelSpace U] [MeasurableSpace L] [BorelSpace L]

/-- After setting the middle Fourier frequency to zero, integration over the last Fourier
frequency equals the Fourier transform in the first coordinate of the middle marginal
of the physical zero slice along the last coordinate. -/
def SchwartzFourierMixedSliceStatement : Prop :=
  ∀ (Φ : 𝓢(P, ℂ)) (x : E),
    (∫ ζ : L, (𝓕 Φ) (toLp 2 (x, toLp 2 (0, ζ)))) =
      𝓕 (fun t : E => ∫ y : U, Φ (toLp 2 (t, toLp 2 (y, 0)))) x

theorem schwartzFourierMixedSlice : SchwartzFourierMixedSliceStatement (E := E) (U := U) (L := L) := by
  intro Φ x
  let Φ' := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ swapMiddle.toContinuousLinearEquiv Φ
  let M := marginal Φ'
  have hM (p : Q) : (𝓕 M) p = (𝓕 Φ') (toLp 2 (p, 0)) := by
    rw [show 𝓕 M = zeroSlice (𝓕 Φ') from fourier_marginal Φ', zeroSlice_apply]
  have hρ (ζ : L) : (𝓕 M) (toLp 2 (x, ζ)) = (𝓕 Φ) (toLp 2 (x, toLp 2 (0, ζ))) := by
    rw [hM, SchwartzMap.fourier_coe]
    have hc : (Φ' : WithLp 2 (Q × U) → ℂ) = (Φ : P → ℂ) ∘ swapMiddle := rfl
    rw [hc, Real.fourier_comp_linearIsometry, swapMiddle_apply, ← SchwartzMap.fourier_coe]
  have hσ (t : E) : zeroSlice M t = ∫ y : U, Φ (toLp 2 (t, toLp 2 (y, 0))) := by
    rw [zeroSlice_apply, marginal_apply]
    apply integral_congr_ae
    filter_upwards with y
    exact congrArg Φ (swapMiddle_apply t y (0 : L))
  calc
    _ = marginal (𝓕 M) x := by rw [marginal_apply]; simp only [hρ]
    _ = _ := by rw [marginal_fourier, SchwartzMap.fourier_coe, funext hσ]

end ThreeFactors

end Langlands.Analysis.SchwartzFourierMarginal
