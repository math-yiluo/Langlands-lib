import Langlands.Analysis.Local.QuotientKernelSupport
import Langlands.Representation.RankinSelberg.RecursiveQuotientIntegrationProof
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.Probability.Kernel.Composition.MeasureComp

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory ProbabilityTheory
open scoped ENNReal CompactlySupported ProbabilityTheory

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) (hH : IsClosed (H : Set G))
  [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  (μH : Measure H) [SFinite μH] [μH.IsMulRightInvariant]

/-- The measure on each actual left coset obtained by translating the subgroup measure. -/
def orbitKernel : Kernel (LeftQuotient H) G := by
  let M : G → Measure G := fun g => Measure.map (fun a : H => a.val * g) μH
  have hinv : ∀ a : H, ∀ g, M (a.val * g) = M g := by
    intro a g
    have he : (fun b : H => b.val * (a.val * g)) =
        (fun b : H => b.val * g) ∘ (fun b : H => b * a) := by
      funext b
      simp [mul_assoc]
    dsimp [M]
    rw [he, ← Measure.map_map (continuous_subtype_val.mul_const g).measurable
      (measurable_mul_const a), map_mul_right_eq_self]
  let κ := descend H M hinv
  have hM : Measurable M := by
    have hf : Measurable (fun z : H × G => z.1.val * z.2) :=
      ((continuous_subtype_val.comp continuous_fst).mul continuous_snd).measurable
    have hm := (Measure.measurable_map _ hf).comp (Measurable.map_prodMk_right (μ := μH))
    simpa only [M, Measure.map_map hf measurable_prodMk_right, Function.comp_def] using hm
  exact ⟨κ, (measurable_quotient_iff H hH κ).2 hM⟩

@[simp] theorem orbitKernel_mk (g : G) :
    orbitKernel H hH μH (Quotient.mk _ g) =
      Measure.map (fun a : H => a.val * g) μH := rfl

/-- Compact-test compatibility determines the composite orbital measure. -/
theorem orbitKernel_comp (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
    (ν : Measure (LeftQuotient H)) (hν : IsCompatible H μG μH ν)
    [IsFiniteMeasureOnCompacts μH] : orbitKernel H hH μH ∘ₘ ν = μG := by
  let κ := orbitKernel H hH μH
  have havg : ∀ f : C_c(G, ℝ), (∀ g, 0 ≤ f g) →
      ∫⁻ g, ENNReal.ofReal (f g) ∂(κ ∘ₘ ν) = ∫⁻ g, ENNReal.ofReal (f g) ∂μG := by
    intro f hf
    have hfm : Measurable (fun g => ENNReal.ofReal (f g)) :=
      (ENNReal.continuous_ofReal.comp f.continuous).measurable
    rw [Measure.lintegral_bind κ.measurable.aemeasurable
      hfm.aemeasurable]
    calc ∫⁻ q, ∫⁻ g, ENNReal.ofReal (f g) ∂κ q ∂ν =
        ∫⁻ q, ENNReal.ofReal (quotientAverageReal H μH f q) ∂ν := by
          apply lintegral_congr
          intro q
          induction q using Quotient.inductionOn with
          | h g =>
            rw [show κ (Quotient.mk _ g) = _ from orbitKernel_mk H hH μH g,
              lintegral_map hfm
                (continuous_subtype_val.mul_const g).measurable]
            exact (ofReal_integral_eq_lintegral_ofReal
              (integrable_subgroup_mul H hH μH f g)
              (Filter.Eventually.of_forall fun a => hf _)).symm
      _ = _ := Langlands.RankinSelberg.RecursiveIntegration.lintegral_quotientAverageReal
        H μG μH ν hν f f.continuous f.hasCompactSupport hf
  have hfin : IsFiniteMeasureOnCompacts (κ ∘ₘ ν) := by
    refine ⟨fun C hC => ?_⟩
    obtain ⟨f, hf1, -, hfcs, hf01⟩ :=
      exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
    let φ : C_c(G, ℝ) := ⟨f, hfcs⟩
    calc (κ ∘ₘ ν) C = ∫⁻ g, C.indicator 1 g ∂(κ ∘ₘ ν) :=
        (lintegral_indicator_one hC.isClosed.measurableSet).symm
      _ ≤ ∫⁻ g, ENNReal.ofReal (φ g) ∂(κ ∘ₘ ν) := by
        apply lintegral_mono
        intro g
        by_cases hg : g ∈ C
        · rw [Set.indicator_of_mem hg]
          change (1 : ℝ≥0∞) ≤ ENNReal.ofReal (f g)
          rw [hf1 hg, Pi.one_apply, ENNReal.ofReal_one]
        · rw [Set.indicator_of_notMem hg]
          exact zero_le
      _ = ∫⁻ g, ENNReal.ofReal (φ g) ∂μG := havg φ fun g => (hf01 g).1
      _ < ⊤ := (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).lintegral_lt_top
  have : (κ ∘ₘ ν).Regular := inferInstance
  have : μG.Regular := inferInstance
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro f
  let φ : C_c(G, ℝ) :=
    ⟨⟨fun g => (f g : ℝ), NNReal.continuous_coe.comp f.continuous⟩,
      f.hasCompactSupport.comp_left NNReal.coe_zero⟩
  have he := havg φ fun g => (f g).coe_nonneg
  rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun g => (f g).coe_nonneg)
      (NNReal.continuous_coe.comp f.continuous).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun g => (f g).coe_nonneg)
      (NNReal.continuous_coe.comp f.continuous).aestronglyMeasurable]
  exact congrArg ENNReal.toReal he

/-- The compact-test Weil formula extends to every measurable nonnegative function. -/
theorem lintegral_orbitKernel (μG : Measure G) [IsFiniteMeasureOnCompacts μG]
    (ν : Measure (LeftQuotient H)) (hν : IsCompatible H μG μH ν)
    [IsFiniteMeasureOnCompacts μH] (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, ∫⁻ g, f g ∂orbitKernel H hH μH q ∂ν = ∫⁻ g, f g ∂μG := by
  rw [← Measure.lintegral_bind (orbitKernel H hH μH).measurable.aemeasurable hf.aemeasurable,
    orbitKernel_comp H hH μH μG ν hν]

end Langlands.QuotientIntegration
