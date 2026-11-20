import Langlands.Representation.GodementJacquet.ComplexCoordinateFourier

/-! # Complementary Fourier marginals on complex coordinate spaces -/

noncomputable section

open MeasureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Analysis

variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]

local notation "A" => ι → ℂ
local notation "B" => κ → ℂ
local notation "C" => η → ℂ

/-- The trace Fourier integral on a product with three coordinate blocks. -/
def complexBlockFourier (a : ℂˣ) (Φ : (A × B) × C → ℂ) (x : (A × B) × C) : ℂ :=
  ∫ y, Φ y * traceCharacter a
    (complexCoordinatePair y.1.1 x.1.1 + complexCoordinatePair y.1.2 x.1.2 +
      complexCoordinatePair y.2 x.2)
    ∂((complexCoordinateMeasure ι a).prod (complexCoordinateMeasure κ a)).prod
      (complexCoordinateMeasure η a)

/-- On a coordinate product, integrate the Fourier transform over the last
frequency block with the second frequency block set to zero. This gives
the transform of the corresponding second-block marginal with the last
input block set to zero. -/
theorem integral_complexBlockFourier_complement (a : ℂˣ)
    (Φ : SchwartzMap ((A × B) × C) ℂ) (x : A) :
    (∫ z : C, complexBlockFourier a Φ ((x, 0), z) ∂complexCoordinateMeasure η a) =
      complexCoordinateFourier a
        (fun p : A => ∫ q : B, Φ ((p, q), 0) ∂complexCoordinateMeasure κ a) x := by
  let μA := complexCoordinateMeasure ι a
  let μB := complexCoordinateMeasure κ a
  let μC := complexCoordinateMeasure η a
  let : μA.IsAddHaarMeasure := complexCoordinateMeasure_isAddHaar a
  let : μB.IsAddHaarMeasure := complexCoordinateMeasure_isAddHaar a
  let : μC.IsAddHaarMeasure := complexCoordinateMeasure_isAddHaar a
  let : (μA.prod μB).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μA μB
  let : ((μA.prod μB).prod μC).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ μC
  let K (p : A × B) := traceCharacter a (complexCoordinatePair p.1 x)
  have hK : Continuous K :=
    ((continuous_traceCharacter a).comp (continuous_complexCoordinatePair x)).comp continuous_fst
  have hnormK (p : A × B) : ‖K p‖ = 1 := norm_traceCharacter a _
  let Φs := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.prodComm ℝ C (A × B)) Φ
  let Ψ : SchwartzMap C ℂ :=
    schwartzBoundedMarginal (μA.prod μB) K hK.measurable (fun p => (hnormK p).le) Φs
  have hΨ (q : C) : Ψ q = ∫ p, Φ (p, q) * K p ∂μA.prod μB := by
    rw [schwartzBoundedMarginal_apply]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun p => mul_comm _ _
  have hFourier (z : C) :
      complexBlockFourier a Φ ((x, 0), z) = complexCoordinateFourier a Ψ z := by
    let h (p : (A × B) × C) := Φ p * K p.1 * traceCharacter a (complexCoordinatePair p.2 z)
    have hi : Integrable h ((μA.prod μB).prod μC) := by
      refine (Φ.integrable (μ := (μA.prod μB).prod μC)).norm.mono'
        ((Φ.continuous.mul (hK.comp continuous_fst)).mul
          (((continuous_traceCharacter a).comp (continuous_complexCoordinatePair z)).comp
            continuous_snd)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => ?_)
      simp [h, hnormK]
    calc
      _ = ∫ p, h p ∂(μA.prod μB).prod μC := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by
          change Φ p * traceCharacter a (complexCoordinatePair p.1.1 x +
            complexCoordinatePair p.1.2 0 + complexCoordinatePair p.2 z) = h p
          rw [complexCoordinatePair_zero_right, add_zero, traceCharacter_add]
          exact (mul_assoc _ _ _).symm
      _ = ∫ q, Ψ q * traceCharacter a (complexCoordinatePair q z) ∂μC := by
        rw [integral_prod_symm _ hi]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun q => by
          simp only [h, hΨ, integral_mul_const]
      _ = _ := rfl
  change (∫ z, complexBlockFourier a Φ ((x, 0), z) ∂μC) = _
  simp only [hFourier]
  rw [show (∫ z, complexCoordinateFourier a Ψ z ∂μC) = Ψ 0 from
    integral_complexCoordinateFourier_zero a Ψ, hΨ]
  let Φ₀ := schwartzSlice Φ (0 : C)
  have hΦ₀ (p : A × B) : Φ₀ p = Φ (p, 0) := schwartzSlice_apply Φ 0 p
  have hi : Integrable (fun p : A × B => Φ (p, 0) * K p) (μA.prod μB) := by
    simp_rw [← hΦ₀]
    exact (Φ₀.integrable (μ := μA.prod μB)).norm.mono'
      (Φ₀.continuous.mul hK).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by simp [hnormK])
  rw [integral_prod _ hi]
  simp only [K, integral_mul_const, complexCoordinateFourier, μA, μB]

end Langlands.GodementJacquet
