import Langlands.Global.RankinSelberg.RealMatrixHeightBounds
import Langlands.Representation.Archimedean.RealStandardModuleGKModule

/-! # Smoothness and growth of all right derivatives in the real coefficient model -/

noncomputable section
open scoped Classical TensorProduct Manifold ContDiff Matrix.Norms.Operator
open Langlands.LocalFactor.Archimedean
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal
namespace RealLocalWhittaker

variable {r : ℕ}

/-- A polynomial height bound, with an explicitly nonnegative constant. -/
def HasPolynomialGrowth (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g, ‖W g‖ ≤ C * realMatrixHeight g ^ N

theorem HasPolynomialGrowth.of_bound {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : ∃ (C : ℝ) (N : ℕ), ∀ g, ‖W g‖ ≤ C * realMatrixHeight g ^ N) :
    HasPolynomialGrowth W := by
  obtain ⟨C, N, hC⟩ := hW
  refine ⟨max C 0, N, le_max_right _ _, fun g => ?_⟩
  exact (hC g).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (pow_nonneg (RealPlaceRestriction.realMatrixHeight_nonneg g) _))

theorem HasPolynomialGrowth.zero : HasPolynomialGrowth (0 : Langlands.GeneralLinear (r + 1) ℝ → ℂ) :=
  ⟨0, 0, le_refl _, by simp⟩

theorem HasPolynomialGrowth.add {W V : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : HasPolynomialGrowth W) (hV : HasPolynomialGrowth V) :
    HasPolynomialGrowth (W + V) := by
  obtain ⟨C, N, hC, hW⟩ := hW
  obtain ⟨D, M, hD, hV⟩ := hV
  refine ⟨C + D, max N M, add_nonneg hC hD, fun g => ?_⟩
  have hH : 1 ≤ realMatrixHeight g :=
    le_trans (by norm_num) (RealPlaceRestriction.two_le_realMatrixHeight (Nat.succ_pos r) g)
  calc
    ‖(W + V) g‖ ≤ ‖W g‖ + ‖V g‖ := norm_add_le _ _
    _ ≤ C * realMatrixHeight g ^ N + D * realMatrixHeight g ^ M :=
      add_le_add (hW g) (hV g)
    _ ≤ C * realMatrixHeight g ^ max N M + D * realMatrixHeight g ^ max N M :=
      add_le_add (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hH (le_max_left N M)) hC)
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH (le_max_right N M)) hD)
    _ = _ := (add_mul _ _ _).symm

theorem HasPolynomialGrowth.smul {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : HasPolynomialGrowth W) (z : ℂ) : HasPolynomialGrowth (z • W) := by
  obtain ⟨C, N, hC, hW⟩ := hW
  refine ⟨‖z‖ * C, N, mul_nonneg (norm_nonneg _) hC, fun g => ?_⟩
  calc
    ‖(z • W) g‖ = ‖z‖ * ‖W g‖ := norm_mul z (W g)
    _ ≤ ‖z‖ * (C * realMatrixHeight g ^ N) :=
      mul_le_mul_of_nonneg_left (hW g) (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Smooth, left-character-equivariant functions with a polynomial height bound. -/
def regularFunctions (r : ℕ) (a : ℝˣ) :
    Submodule ℂ (Langlands.GeneralLinear (r + 1) ℝ → ℂ) where
  carrier := {W |
    (∀ u ∈ GeneralLinear.upperUnipotent (r + 1) ℝ, ∀ g,
      W (u * g) = realWhittakerCharacter a u * W g) ∧
    ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ W ∧
    HasPolynomialGrowth W}
  zero_mem' := ⟨by simp, contMDiff_const, HasPolynomialGrowth.zero⟩
  add_mem' hW hV := ⟨fun u hu g => by
      simp only [Pi.add_apply, hW.1 u hu g, hV.1 u hu g, mul_add],
    hW.2.1.add hV.2.1, hW.2.2.add hV.2.2⟩
  smul_mem' z _ hW := ⟨fun u hu g => by
      simp only [Pi.smul_apply, smul_eq_mul, hW.1 u hu g]
      ring,
    ((z • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp hW.2.1,
    hW.2.2.smul z⟩

theorem model_le_regularFunctions (ds : List RealBlock) (a : ℝˣ) :
    realWhittakerModel r ds a ≤ regularFunctions r a := by
  refine iSup_le fun B => iSup_le fun hB => ?_
  rintro _ ⟨f, rfl⟩
  exact ⟨hB.1 f, hB.2.1 f, HasPolynomialGrowth.of_bound (hB.2.2.1 f)⟩

set_option backward.isDefEq.respectTransparency false in
theorem contMDiff_of_mem_model {ds : List RealBlock} {a : ℝˣ}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : W ∈ realWhittakerModel r ds a) :
    ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ W :=
  (model_le_regularFunctions ds a hW).2.1

theorem growth_of_mem_model {ds : List RealBlock} {a : ℝˣ}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : W ∈ realWhittakerModel r ds a) : HasPolynomialGrowth W :=
  (model_le_regularFunctions ds a hW).2.2

set_option backward.isDefEq.respectTransparency false in
/-- The specified coefficient model is stable under every real matrix right derivative. -/
theorem rightDerivative_mem_model {ds : List RealBlock} {a : ℝˣ}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : W ∈ realWhittakerModel r ds a)
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) :
    Archimedean.rightDerivative (Archimedean.matrixModel ℝ (r + 1)) X W ∈
      realWhittakerModel r ds a := by
  let V : Submodule ℂ (Langlands.GeneralLinear (r + 1) ℝ → ℂ) :=
    { carrier := {W |
        ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ W ∧
        Archimedean.rightDerivative (Archimedean.matrixModel ℝ (r + 1)) X W ∈
          realWhittakerModel r ds a}
      zero_mem' := ⟨contMDiff_const, by
        have hz : Archimedean.rightDerivative (Archimedean.matrixModel ℝ (r + 1)) X
            (0 : Langlands.GeneralLinear (r + 1) ℝ → ℂ) = 0 := by
          funext g
          simp only [Archimedean.rightDerivative, Pi.zero_apply, mfderiv_const]
          rfl
        rw [hz]
        exact Submodule.zero_mem _⟩
      add_mem' := fun hA hB => ⟨hA.1.add hB.1, by
        rw [Archimedean.rightDerivative_add hA.1 hB.1]
        exact Submodule.add_mem _ hA.2 hB.2⟩
      smul_mem' := fun z _ hA =>
        ⟨((z • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp hA.1, by
          rw [Archimedean.rightDerivative_smul hA.1]
          exact Submodule.smul_mem _ z hA.2⟩ }
  have hle : realWhittakerModel r ds a ≤ V := by
    refine iSup_le fun B => iSup_le fun hB => ?_
    rintro _ ⟨f, rfl⟩
    refine ⟨hB.2.1 f, ?_⟩
    let f' : Automorphic.realStandardKFinite (r + 1) ds :=
      Archimedean.realStandardLie (r + 1) ds ((1 : ℂ) ⊗ₜ[ℝ] X) f
    have he := hB.2.2.2.2 X f f'
      (Archimedean.realStandardLie_one_tmul_apply_coe (r + 1) ds X f)
    rw [← he]
    exact Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f', rfl⟩)
  exact (hle hW).2

set_option backward.isDefEq.respectTransparency false in
/-- Compose right derivatives in the order displayed by a list, with the first direction
acting after the derivatives in the tail. -/
def iteratedRightDerivative (r : ℕ)
    (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ))
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) :
    Langlands.GeneralLinear (r + 1) ℝ → ℂ :=
  Xs.foldr (fun X f => Archimedean.rightDerivative (Archimedean.matrixModel ℝ (r + 1)) X f) W

theorem iteratedRightDerivative_mem_model {ds : List RealBlock} {a : ℝˣ}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : W ∈ realWhittakerModel r ds a)
    (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) :
    iteratedRightDerivative r Xs W ∈ realWhittakerModel r ds a := by
  induction Xs with
  | nil => exact hW
  | cons X Xs ih =>
    simp only [iteratedRightDerivative, List.foldr_cons]
    exact rightDerivative_mem_model ih X

end RealLocalWhittaker

/-- All iterated real matrix right derivatives of a function in the specified real
Whittaker model are smooth, left-character equivariant and polynomially bounded. -/
def RealLocalWhittakerRegularityStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock) (a : ℝˣ)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ),
    W ∈ realWhittakerModel r ds a →
  ∀ Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ),
    RealLocalWhittaker.iteratedRightDerivative r Xs W ∈ RealLocalWhittaker.regularFunctions r a

theorem realLocalWhittakerRegularity : RealLocalWhittakerRegularityStatement :=
  fun _ ds a _ hW Xs => RealLocalWhittaker.model_le_regularFunctions ds a
    (RealLocalWhittaker.iteratedRightDerivative_mem_model hW Xs)

end Langlands.Global.RankinSelbergGlobal
