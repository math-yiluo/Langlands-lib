import Langlands.HarmonicAnalysis.Distribution.RenardHaarStatements
import Langlands.HarmonicAnalysis.RowTensorDecompositionProof
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Integral

/-! # Positivity of Haar integration and the actual density embedding -/

noncomputable section

open MeasureTheory
open Langlands.Hecke.TestFunction

namespace Langlands.HarmonicAnalysis.Distribution.RenardHaar

universe u

section Spaces

variable {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

theorem ofMeasure_positive : IsPositive (ofMeasure μ) := by
  intro f hf hnonneg
  have hfint := test_integrable μ f
  constructor
  · have hi := integral_im hfint
    change (∫ x, (f x).im ∂μ) = (∫ x, f x ∂μ).im at hi
    rw [ofMeasure_apply, ← hi]
    simp only [(hnonneg _).1, integral_zero]
  · obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra! h
      exact hf (Hecke.TestFunction.ext h)
    have hxre : (f x).re ≠ 0 := by
      intro h
      exact hx (Complex.ext h (hnonneg x).1)
    have hr := integral_re hfint
    change (∫ x, (f x).re ∂μ) = (∫ x, f x ∂μ).re at hr
    rw [ofMeasure_apply, ← hr]
    exact integral_pos_of_integrable_nonneg_nonzero
      (Complex.continuous_re.comp f.continuous) hfint.re
      (fun x => (hnonneg x).2) hxre

omit [MeasurableSpace X] [BorelSpace X] in
theorem characteristic_nonnegative {U : Set X} (hU : IsClopen U) (hc : IsCompact U) :
    IsNonnegativeTest (characteristic hU hc) := by
  intro x
  by_cases hx : x ∈ U <;> simp [characteristic_apply, hx]

omit [MeasurableSpace X] [BorelSpace X] in
theorem characteristic_ne_zero {U : Set X} (hU : IsClopen U) (hc : IsCompact U)
    (hne : U.Nonempty) : characteristic hU hc ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := hne
  have := congrArg (fun f : SchwartzBruhat X => f x) h
  simp [characteristic_apply, hx] at this

theorem ofMeasure_characteristic_ne_zero {U : Set X} (hU : IsClopen U)
    (hc : IsCompact U) (hne : U.Nonempty) :
    ofMeasure μ (characteristic hU hc) ≠ 0 := by
  have h := ofMeasure_positive μ _ (characteristic_ne_zero hU hc hne)
    (characteristic_nonnegative hU hc)
  intro hz
  simpa [hz] using h.2

variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

theorem density_support (f : LocallyConstant X ℂ) :
    support (density μ f) = Function.support f := by
  have hfclosed : IsClosed (Function.support f) :=
    (f.isLocallyConstant.isClopen_fiber 0).compl.isClosed
  apply Set.Subset.antisymm
  · apply support_subset_of_mem_supportedOn hfclosed
    intro φ hφ
    rw [density_apply]
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : f x = 0
    · simp [hx]
    · simp [hφ x hx]
  · intro x hx
    by_contra hxs
    have hnhds : (support (density μ f))ᶜ ∩ {y | f y = f x} ∈ nhds x :=
      Filter.inter_mem
        ((isClosed_support _).isOpen_compl.mem_nhds hxs)
        ((f.isLocallyConstant.isOpen_fiber (f x)).mem_nhds rfl)
    obtain ⟨U, hc, hU, hxU, hUsub⟩ := exists_compact_clopen hnhds
    let φ := characteristic hU hc
    have hzero : density μ f φ = 0 := by
      apply mem_supportedOn_support (density μ f)
      intro y hy
      apply Set.indicator_of_notMem
      intro hyU
      exact (hUsub hyU).1 hy
    have hvalue : density μ f φ = f x * ofMeasure μ φ := by
      rw [density_apply, ofMeasure_apply, ← integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change f y * φ y = f x * φ y
      by_cases hy : y ∈ U
      · rw [(hUsub hy).2]
      · simp [φ, characteristic_apply, hy]
    exact (mul_ne_zero hx (ofMeasure_characteristic_ne_zero μ hU hc ⟨x, hxU⟩))
      (hvalue.symm.trans hzero)

theorem density_injective : Function.Injective (density μ) := by
  intro f g hfg
  have hz : density μ (f - g) = 0 := by rw [map_sub, hfg, sub_self]
  have hs := density_support μ (f - g)
  rw [hz, support_zero] at hs
  apply sub_eq_zero.mp
  ext x
  have hx : x ∉ Function.support (f - g) := by rw [← hs]; simp
  exact not_not.mp hx

theorem testDensity_compactlySupported (f : SchwartzBruhat X) :
    testDensity μ f ∈ compactlySupported := by
  change IsCompact (support (density μ
    (⟨(f : X → ℂ), f.locallyConstant⟩ : LocallyConstant X ℂ)))
  rw [density_support]
  exact isCompact_support f

end Spaces

theorem densityEmbedding : DensityEmbeddingStatement.{u} := by
  intro G _ _ _ _ _ _ _ _ μ _
  exact ⟨density_injective μ, density_support μ, testDensity_compactlySupported μ⟩

theorem ofMeasure_leftInvariant {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant] :
    IsLeftInvariant (ofMeasure μ) := by
  intro g
  ext f
  simpa only [GroupAction.leftDistributions_apply, ofMeasure_apply,
    GroupAction.leftTests_apply, inv_inv] using
    integral_mul_left_eq_self (μ := μ) (f : G → ℂ) g

end Langlands.HarmonicAnalysis.Distribution.RenardHaar
