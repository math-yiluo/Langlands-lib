import Langlands.HarmonicAnalysis.Distribution.OpenChartPushforward
import Langlands.HarmonicAnalysis.Distribution.RenardConvolutionDensityProof

/-! # Smoothed distribution evaluation after test pushforward -/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution

open MeasureTheory Set Function
open Hecke.TestFunction (leftTranslate)

variable {X G : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]

/-- Distribution evaluation of a test convolution integrates the evaluations of
the translated second test against the first test. -/
theorem eval_convolution_eq_integral_leftTranslate [T2Space G] [BorelSpace G]
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν]
    (D : Distribution G) (f g : SchwartzBruhat G) :
    D (Hecke.TestFunction.convolution ν f g) = ∫ x, f x * D (leftTranslate x g) ∂ν := by
  let k : SchwartzBruhat (G × G) := SchwartzBruhat.compLeftInverse (SchwartzBruhat.tensor f g)
    (fun p : G × G => (p.2, p.2⁻¹ * p.1))
    (fun p : G × G => (p.1 * p.2, p.1))
    (continuous_snd.prodMk (continuous_snd.inv.mul continuous_fst))
    ((continuous_fst.mul continuous_snd).prodMk continuous_fst)
    (by intro p; ext <;> simp)
  have hk : SchwartzBruhat.partialIntegral k ν = Hecke.TestFunction.convolution ν f g :=
    Hecke.TestFunction.ext fun _ => rfl
  rw [← hk, distribution_partialIntegral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have hslice : SchwartzBruhat.sliceFst k x = f x • leftTranslate x g :=
      Hecke.TestFunction.ext fun _ => rfl
    change D (SchwartzBruhat.sliceFst k x) = f x * D (leftTranslate x g)
    rw [hslice, map_smul]
    rfl

omit [MeasurableSpace G] in
/-- Smoothing by a scalar test gives a locally constant function of the translating
element. -/
theorem isLocallyConstant_eval_leftTranslate [T2Space G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] (D : Distribution G) (g : SchwartzBruhat G) :
    IsLocallyConstant (fun x => D (leftTranslate x g)) := by
  let g' := Hecke.TestFunction.inversion g
  have h : Hecke.TestFunction.inversion g' = g := Hecke.TestFunction.ext fun x => by
    simp [g']
  have hLoc := leftConvolveTest_locallyConstant D g'
  change IsLocallyConstant (fun x => D (leftTranslate x (Hecke.TestFunction.inversion g'))) at hLoc
  rwa [h] at hLoc

/-- After smoothing a distribution by a scalar test, evaluating a pushforward
equals integrating the translated-test evaluations pulled back to the source. -/
def SmoothedPushforwardEvaluationStatement [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [BorelSpace G] (μ : Measure X) (ν : Measure G) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
    (p : X → G) (P : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat G) : Prop :=
  Continuous p → SchwartzBruhat.IsTestPushforward μ ν p P →
  ∀ (D : Distribution G) (f : SchwartzBruhat X) (g : SchwartzBruhat G),
    D (Hecke.TestFunction.convolution ν (P f) g) = ∫ x, f x * D (leftTranslate (p x) g) ∂μ

theorem smoothedPushforwardEvaluation [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [BorelSpace G]
    (μ : Measure X) (ν : Measure G) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
    (p : X → G) (P : SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat G) :
    SmoothedPushforwardEvaluationStatement μ ν p P := by
  intro hp hP D f g
  let φ : LocallyConstant G ℂ := ⟨fun y => D (leftTranslate y g),
    isLocallyConstant_eval_leftTranslate D g⟩
  obtain ⟨test, htest⟩ := exists_testFunction_agrees_on_compact
    ((Hecke.TestFunction.isCompact_support f).image hp) φ
  have htarget : ∀ y, P f y * D (leftTranslate y g) = P f y * test y := by
    intro y
    by_cases hy : P f y = 0
    · rw [hy, zero_mul, zero_mul]
    · exact congrArg (P f y * ·) (htest y (hP.support_apply_subset hp f hy)).symm
  have hsource : ∀ x, f x * test (p x) = f x * D (leftTranslate (p x) g) := by
    intro x
    by_cases hx : f x = 0
    · rw [hx, zero_mul, zero_mul]
    · exact congrArg (f x * ·) (htest (p x) ⟨x, hx, rfl⟩)
  rw [eval_convolution_eq_integral_leftTranslate]
  calc
    _ = ∫ y, P f y * test y ∂ν := integral_congr_ae (Filter.Eventually.of_forall htarget)
    _ = ∫ x, f x * test (p x) ∂μ := hP f test
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hsource)

end Langlands.HarmonicAnalysis.Distribution
