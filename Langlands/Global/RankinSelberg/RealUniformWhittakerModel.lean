import Langlands.Global.RankinSelberg.RealLocalWhittakerProperties

/-! # A real coefficient model with one exponent for all source vectors -/

noncomputable section
open scoped Classical TensorProduct Manifold ContDiff Matrix.Norms.Operator
open Langlands.LocalFactor.Archimedean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

/-- A specified real coefficient intertwiner with one growth exponent for all source vectors.
The constant may depend on the vector. -/
def IsRealUniformWhittakerIntertwiner (r : ℕ) (ds : List RealBlock) (a : ℝˣ)
    (B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)) : Prop :=
  IsRealWhittakerIntertwiner r ds a B ∧
    ∃ N : ℕ, ∀ f : Automorphic.realStandardKFinite (r + 1) ds,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Langlands.GeneralLinear (r + 1) ℝ,
        ‖B f g‖ ≤ C * realMatrixHeight g ^ N

/-- The span of ranges of coefficient maps having a common exponent before source vectors.
No equality with a continuous globalization is asserted. -/
def realUniformWhittakerModel (r : ℕ) (ds : List RealBlock) (a : ℝˣ) :
    Submodule ℂ (Langlands.GeneralLinear (r + 1) ℝ → ℂ) :=
  ⨆ (B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ))
    (_ : IsRealUniformWhittakerIntertwiner r ds a B), LinearMap.range B

namespace RealUniformWhittaker

open RealLocalWhittaker
variable {r : ℕ}

theorem model_le_model (ds : List RealBlock) (a : ℝˣ) :
    realUniformWhittakerModel r ds a ≤ realWhittakerModel r ds a := by
  refine iSup_le fun B => iSup_le fun hB => ?_
  exact le_iSup_of_le B (le_iSup_of_le hB.1 le_rfl)

theorem contMDiff_iteratedRightDerivative
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ W)
    (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) :
    ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞
      (iteratedRightDerivative r Xs W) := by
  induction Xs with
  | nil => exact hW
  | cons X Xs ih => exact Archimedean.contMDiff_rightDerivative ih X

theorem iteratedRightDerivative_add
    {W V : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ W)
    (hV : ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ V)
    (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) :
    iteratedRightDerivative r Xs (W + V) =
      iteratedRightDerivative r Xs W + iteratedRightDerivative r Xs V := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change Archimedean.rightDerivative _ X (iteratedRightDerivative r Xs (W + V)) = _
    rw [ih, Archimedean.rightDerivative_add
      (contMDiff_iteratedRightDerivative hW Xs) (contMDiff_iteratedRightDerivative hV Xs)]
    rfl

theorem iteratedRightDerivative_smul
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ W)
    (z : ℂ) (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) :
    iteratedRightDerivative r Xs (z • W) = z • iteratedRightDerivative r Xs W := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change Archimedean.rightDerivative _ X (iteratedRightDerivative r Xs (z • W)) = _
    rw [ih, Archimedean.rightDerivative_smul (contMDiff_iteratedRightDerivative hW Xs)]
    rfl

theorem iteratedRightDerivative_zero
    (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) :
    iteratedRightDerivative r Xs (0 : Langlands.GeneralLinear (r + 1) ℝ → ℂ) = 0 := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change Archimedean.rightDerivative _ X (iteratedRightDerivative r Xs 0) = _
    rw [ih]
    refine funext fun g => ?_
    simp only [Archimedean.rightDerivative, Pi.zero_apply, mfderiv_const]
    rfl

/-- One exponent works for every finite matrix right-derivative word of this function. -/
def HasUniformDerivativeGrowth (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) : Prop :=
  ∃ N : ℕ, ∀ Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖iteratedRightDerivative r Xs W g‖ ≤ C * realMatrixHeight g ^ N

/-- Smooth functions with a common polynomial exponent for all derivative words. -/
def uniformGrowthFunctions (r : ℕ) : Submodule ℂ (Langlands.GeneralLinear (r + 1) ℝ → ℂ) where
  carrier := {W |
    ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ W ∧
      HasUniformDerivativeGrowth W}
  zero_mem' := ⟨contMDiff_const, 0, fun Xs => ⟨0, le_refl _, by
    rw [iteratedRightDerivative_zero]
    simp⟩⟩
  add_mem' := by
    rintro W V ⟨hW, N, hN⟩ ⟨hV, M, hM⟩
    refine ⟨hW.add hV, max N M, fun Xs => ?_⟩
    obtain ⟨C, hC0, hC⟩ := hN Xs
    obtain ⟨D, hD0, hD⟩ := hM Xs
    refine ⟨C + D, add_nonneg hC0 hD0, fun g => ?_⟩
    rw [iteratedRightDerivative_add hW hV Xs]
    have hH : 1 ≤ realMatrixHeight g :=
      le_trans (by norm_num) (RealPlaceRestriction.two_le_realMatrixHeight (Nat.succ_pos r) g)
    calc
      _ ≤ ‖iteratedRightDerivative r Xs W g‖ + ‖iteratedRightDerivative r Xs V g‖ :=
        norm_add_le _ _
      _ ≤ C * realMatrixHeight g ^ N + D * realMatrixHeight g ^ M :=
        add_le_add (hC g) (hD g)
      _ ≤ C * realMatrixHeight g ^ max N M + D * realMatrixHeight g ^ max N M :=
        add_le_add (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hH (le_max_left N M)) hC0)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH (le_max_right N M)) hD0)
      _ = _ := (add_mul _ _ _).symm
  smul_mem' := by
    rintro z W ⟨hW, N, hN⟩
    refine ⟨((z • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp hW,
      N, fun Xs => ?_⟩
    obtain ⟨C, hC0, hC⟩ := hN Xs
    refine ⟨‖z‖ * C, mul_nonneg (norm_nonneg _) hC0, fun g => ?_⟩
    rw [iteratedRightDerivative_smul hW z Xs]
    calc
      _ = ‖z‖ * ‖iteratedRightDerivative r Xs W g‖ := norm_mul _ _
      _ ≤ ‖z‖ * (C * realMatrixHeight g ^ N) :=
        mul_le_mul_of_nonneg_left (hC g) (norm_nonneg _)
      _ = _ := (mul_assoc _ _ _).symm

theorem exists_iteratedRightDerivative_eq_coefficient
    {ds : List RealBlock} {a : ℝˣ}
    {B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B)
    (f : Automorphic.realStandardKFinite (r + 1) ds)
    (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) :
    ∃ f' : Automorphic.realStandardKFinite (r + 1) ds,
      iteratedRightDerivative r Xs (B f) = B f' := by
  induction Xs with
  | nil => exact ⟨f, rfl⟩
  | cons X Xs ih =>
    obtain ⟨f', hf'⟩ := ih
    refine ⟨Archimedean.realStandardLie (r + 1) ds ((1 : ℂ) ⊗ₜ[ℝ] X) f', ?_⟩
    change Archimedean.rightDerivative _ X (iteratedRightDerivative r Xs (B f)) = _
    rw [hf']
    exact (hB.2.2.2.2 X f' _
      (Archimedean.realStandardLie_one_tmul_apply_coe (r + 1) ds X f')).symm

theorem model_le_uniformGrowthFunctions (ds : List RealBlock) (a : ℝˣ) :
    realUniformWhittakerModel r ds a ≤ uniformGrowthFunctions r := by
  refine iSup_le fun B => iSup_le fun hB => ?_
  rintro _ ⟨f, rfl⟩
  refine ⟨hB.1.2.1 f, ?_⟩
  obtain ⟨N, hN⟩ := hB.2
  refine ⟨N, fun Xs => ?_⟩
  obtain ⟨f', hf'⟩ := exists_iteratedRightDerivative_eq_coefficient hB.1 f Xs
  obtain ⟨C, hC0, hC⟩ := hN f'
  exact ⟨C, hC0, by simpa only [hf'] using hC⟩

theorem uniformDerivativeGrowth_of_mem_model
    {ds : List RealBlock} {a : ℝˣ} {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : W ∈ realUniformWhittakerModel r ds a) : HasUniformDerivativeGrowth W :=
  (model_le_uniformGrowthFunctions ds a hW).2

theorem iteratedRightDerivative_mem_regularFunctions
    {ds : List RealBlock} {a : ℝˣ} {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : W ∈ realUniformWhittakerModel r ds a)
    (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) :
    iteratedRightDerivative r Xs W ∈ RealLocalWhittaker.regularFunctions r a :=
  realLocalWhittakerRegularity r ds a W (model_le_model ds a hW) Xs

end RealUniformWhittaker

/-- Every member of the refined real coefficient space has smooth character-equivariant
derivative words and one polynomial exponent for all words. -/
def RealUniformWhittakerRegularityStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock) (a : ℝˣ)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ),
    W ∈ realUniformWhittakerModel r ds a →
      (∀ Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ),
        RealLocalWhittaker.iteratedRightDerivative r Xs W ∈
          RealLocalWhittaker.regularFunctions r a) ∧
      RealUniformWhittaker.HasUniformDerivativeGrowth W

theorem realUniformWhittakerRegularity : RealUniformWhittakerRegularityStatement :=
  fun _ _ _ _ hW => ⟨RealUniformWhittaker.iteratedRightDerivative_mem_regularFunctions hW,
    RealUniformWhittaker.uniformDerivativeGrowth_of_mem_model hW⟩

end Langlands.Global.RankinSelbergGlobal
