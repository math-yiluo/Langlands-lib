import Langlands.Representation.GodementJacquet.ComplexCoordinateFourier

/-! # Fourier integration on complementary affine coordinate slices -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Analysis

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
local notation "A" => ι → ℂ
local notation "B" => κ → ℂ

private theorem complexCoordinatePair_sub_left (x y z : B) :
    complexCoordinatePair (x - y) z = complexCoordinatePair x z - complexCoordinatePair y z := by
  simp only [complexCoordinatePair, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- Fourier inversion at an arbitrary point in the finite complex trace space. -/
theorem integral_complexCoordinateFourier_translate (a : ℂˣ) (Φ : SchwartzMap B ℂ) (b : B) :
    (∫ y, complexCoordinateFourier a Φ y * traceCharacter a (-complexCoordinatePair b y)
      ∂complexCoordinateMeasure κ a) = Φ b := by
  let μ := complexCoordinateMeasure κ a
  let Ψ := Φ.compSubConstCLM ℂ (-b)
  have hΨ (y : B) : complexCoordinateFourier a Ψ y =
      complexCoordinateFourier a Φ y * traceCharacter a (-complexCoordinatePair b y) := by
    let F (x : B) := Φ x * traceCharacter a (complexCoordinatePair (x - b) y)
    calc
      _ = ∫ x, F (x + b) ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          change Ψ x * traceCharacter a (complexCoordinatePair x y) = F (x + b)
          simp only [Ψ, F, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, add_sub_cancel_right]
      _ = ∫ x, F x ∂μ := integral_add_right_eq_self F b
      _ = _ := by
        have he (x : B) : F x = Φ x * traceCharacter a (complexCoordinatePair x y) *
            traceCharacter a (-complexCoordinatePair b y) := by
          change Φ x * traceCharacter a (complexCoordinatePair (x - b) y) = _
          rw [complexCoordinatePair_sub_left, sub_eq_add_neg, traceCharacter_add, mul_assoc]
        simp only [he, integral_mul_const, complexCoordinateFourier, μ]
  simp_rw [← hΨ, integral_complexCoordinateFourier_zero a Ψ]
  simp [Ψ]

/-- The finite-product Fourier integral with two blocks for the positive trace character. -/
def complexTwoBlockFourier (a : ℂˣ) (Φ : A × B → ℂ) (z : A × B) : ℂ :=
  ∫ x, Φ x * traceCharacter a
    (complexCoordinatePair x.1 z.1 + complexCoordinatePair x.2 z.2)
    ∂(complexCoordinateMeasure ι a).prod (complexCoordinateMeasure κ a)

/-- Fourier transformation along one block followed by affine inversion in the other. -/
theorem integral_complexTwoBlockFourier_affineSlice (a : ℂˣ)
    (Φ : SchwartzMap (A × B) ℂ) (z : A) (b : B) :
    Integrable (fun y => complexTwoBlockFourier a Φ (z, y) *
      traceCharacter a (-complexCoordinatePair b y)) (complexCoordinateMeasure κ a) ∧
    Integrable (fun x => Φ (x, b) * traceCharacter a (complexCoordinatePair x z))
      (complexCoordinateMeasure ι a) ∧
    (∫ y, complexTwoBlockFourier a Φ (z, y) *
      traceCharacter a (-complexCoordinatePair b y) ∂complexCoordinateMeasure κ a) =
      ∫ x, Φ (x, b) * traceCharacter a (complexCoordinatePair x z) ∂complexCoordinateMeasure ι a := by
  let μA := complexCoordinateMeasure ι a
  let μB := complexCoordinateMeasure κ a
  let : μA.IsAddHaarMeasure := complexCoordinateMeasure_isAddHaar a
  let : μB.IsAddHaarMeasure := complexCoordinateMeasure_isAddHaar a
  let : (μA.prod μB).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μA μB
  let K (x : A) := traceCharacter a (complexCoordinatePair x z)
  have hK : Continuous K := (continuous_traceCharacter a).comp (continuous_complexCoordinatePair z)
  let Φs := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.prodComm ℝ B A) Φ
  let Ψ : SchwartzMap B ℂ :=
    schwartzBoundedMarginal μA K hK.measurable (fun x => (norm_traceCharacter a _).le) Φs
  have hΨ (y : B) : Ψ y = ∫ x, Φ (x, y) * K x ∂μA := by
    rw [schwartzBoundedMarginal_apply]
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have hfourier (y : B) : complexTwoBlockFourier a Φ (z, y) = complexCoordinateFourier a Ψ y := by
    let F (q : A × B) := Φ q * K q.1 * traceCharacter a (complexCoordinatePair q.2 y)
    have hF : Integrable F (μA.prod μB) := by
      refine (Φ.integrable (μ := μA.prod μB)).norm.mono'
        ((Φ.continuous.mul (hK.comp continuous_fst)).mul
          (((continuous_traceCharacter a).comp (continuous_complexCoordinatePair y)).comp
            continuous_snd)).aestronglyMeasurable
        (Eventually.of_forall fun p => ?_)
      simp [F, K]
    calc
      _ = ∫ q, F q ∂μA.prod μB := by
        apply integral_congr_ae
        exact Eventually.of_forall fun q => by
          change Φ q * traceCharacter a (complexCoordinatePair q.1 z + complexCoordinatePair q.2 y) =
            Φ q * K q.1 * traceCharacter a (complexCoordinatePair q.2 y)
          rw [traceCharacter_add]
          exact (mul_assoc _ _ _).symm
      _ = ∫ y', Ψ y' * traceCharacter a (complexCoordinatePair y' y) ∂μB := by
        rw [integral_prod_symm _ hF]
        apply integral_congr_ae
        exact Eventually.of_forall fun y' => by simp only [F, hΨ, integral_mul_const]
      _ = _ := rfl
  refine ⟨?_, ?_, ?_⟩
  · have hcont : Continuous (complexCoordinateFourier a Ψ) := by
      obtain ⟨FW, hFW⟩ := exists_schwartz_complexCoordinateFourier a Ψ
      rw [← hFW]
      exact FW.continuous
    have hphase : Continuous (fun y : B => traceCharacter a (-complexCoordinatePair b y)) := by
      apply (continuous_traceCharacter a).comp
      unfold complexCoordinatePair
      fun_prop
    simp only [hfourier]
    refine (integrable_complexCoordinateFourier a Ψ).norm.mono'
      (hcont.mul hphase).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    simp
  · let Φb := schwartzSlice Φ b
    have he (x : A) : Φb x = Φ (x, b) := schwartzSlice_apply Φ b x
    simp_rw [← he]
    exact (Φb.integrable (μ := μA)).norm.mono'
      (Φb.continuous.mul hK).aestronglyMeasurable
      (Eventually.of_forall fun x => by simp)
  · simp_rw [hfourier, integral_complexCoordinateFourier_translate a Ψ b, hΨ]
    rfl

end Langlands.GodementJacquet
