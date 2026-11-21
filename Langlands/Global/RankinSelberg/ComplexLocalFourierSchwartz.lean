import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.RingTheory.Complex

/-! # Schwartz closure for the complex trace Fourier transform -/

noncomputable section

open MeasureTheory Langlands.LocalFactor.Archimedean
open scoped FourierTransform InnerProductSpace NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

/-- The Fourier transform with the Library's positive complex trace pairing and
self-dual product measure is represented by a continuous linear map on Schwartz space. -/
def ComplexLocalFourierContinuityStatement (n : ℕ) : Prop :=
  ∀ a : ℂˣ, ∃ F : SchwartzMap (Fin n → ℂ) ℂ →L[ℂ] SchwartzMap (Fin n → ℂ) ℂ,
    ∀ Φ, (F Φ : (Fin n → ℂ) → ℂ) = complexFourierTransform a Φ

theorem complexLocalFourierContinuity (n : ℕ) : ComplexLocalFourierContinuityStatement n := by
  intro a
  let V := EuclideanSpace ℂ (Fin n)
  let : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  let E : (Fin n → ℂ) ≃L[ℝ] V := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm
  let a₂ : ℂ := 2 * (a : ℂ)
  have ha₂ : a₂ ≠ 0 := mul_ne_zero (by norm_num) a.ne_zero
  let K : ℂ ≃ₗ[ℝ] ℂ :=
    ((LinearEquiv.smulOfNeZero ℂ ℂ a₂ ha₂).restrictScalars ℝ).trans
      Complex.conjCLE.toLinearEquiv
  let J : (Fin n → ℂ) ≃L[ℝ] V :=
    (LinearEquiv.piCongrRight (fun _ : Fin n => K)).toContinuousLinearEquiv.trans E
  have hPair (y x : Fin n → ℂ) :
      ⟪E y, J x⟫_ℝ = Algebra.trace ℝ ℂ ((a : ℂ) * ∑ j : Fin n, y j * x j) := by
    change Complex.re ⟪E y, J x⟫_ℂ = _
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply']
    change Complex.re (∑ j : Fin n, starRingEnd ℂ (y j) * starRingEnd ℂ (a₂ * x j)) = _
    rw [Algebra.trace_complex_apply]
    simp only [← map_mul, ← map_sum, Complex.conj_re]
    have hSum : (∑ j : Fin n, y j * (a₂ * x j)) =
        2 * ((a : ℂ) * ∑ j : Fin n, y j * x j) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [a₂]
      ring
    rw [hSum]
    simp [Complex.mul_re]
  let ν := (complexSelfDualMeasure a).measure
  let : ν.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  let μ : Measure (Fin n → ℂ) := Measure.pi (fun _ : Fin n => ν)
  let : μ.IsAddHaarMeasure := by dsimp [μ]; infer_instance
  let c := Measure.addHaarScalarFactor (μ.map E) (volume : Measure V)
  have hMeasure : μ.map E = c • (volume : Measure V) :=
    Measure.isAddLeftInvariant_eq_smul _ _
  let pull := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) E.symm
  let transform := FourierTransform.fourierInvCLM ℂ (SchwartzMap V ℂ)
  let push := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) J
  let T := (c : ℂ) • (push.comp (transform.comp pull))
  refine ⟨T, fun Φ => funext fun x => ?_⟩
  let H := pull Φ
  let F (v : V) := ((Real.fourierChar ⟪v, J x⟫_ℝ : Circle) : ℂ) * H v
  calc
    T Φ x = (c : ℝ) • ∫ v, F v := by
      simp only [T, push, ContinuousLinearMap.comp_apply,
        transform, FourierTransform.fourierInvCLM_apply, ← Complex.real_smul,
        smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        Function.comp_apply, SchwartzMap.fourierInv_coe, Real.fourierInv_eq, Circle.smul_def,
        smul_eq_mul, F, H]
    _ = ∫ v, F v ∂μ.map E := by
      rw [hMeasure, integral_smul_nnreal_measure, NNReal.smul_def]
    _ = ∫ y, F (E y) ∂μ := E.toHomeomorph.measurableEmbedding.integral_map F
    _ = complexFourierTransform a Φ x := by
      change (∫ y, F (E y) ∂μ) =
        ∫ y, Φ y * (complexScaledCharacter a).complex (∑ j : Fin n, y j * x j) ∂μ
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun y => ?_
      simp only [F, hPair, H, pull, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        ContinuousLinearEquiv.symm_apply_apply,
        HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, complexScaledCharacter_apply]
      exact mul_comm _ _

/-- The exact Fourier transform has a Schwartz representative agreeing at every point. -/
theorem exists_schwartz_complexFourierTransform {n : ℕ} (a : ℂˣ)
    (Φ : SchwartzMap (Fin n → ℂ) ℂ) :
    ∃ Ψ : SchwartzMap (Fin n → ℂ) ℂ, (Ψ : (Fin n → ℂ) → ℂ) = complexFourierTransform a Φ := by
  obtain ⟨F, hF⟩ := complexLocalFourierContinuity n a
  exact ⟨F Φ, hF Φ⟩

end Langlands.Global.RankinSelbergGlobal
