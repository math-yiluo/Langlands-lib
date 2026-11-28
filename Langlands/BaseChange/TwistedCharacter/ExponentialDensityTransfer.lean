import Langlands.BaseChange.TwistedCharacter.ExponentialTraceFourier
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Returning an additive density through the exponential chart -/

noncomputable section

set_option autoImplicit false

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis Set Function _root_.Topology
open Hecke.TestFunction (pullback pullback_apply)

section OpenCharts

variable {X Y K : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
  [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [CompactSpace K]
  {i : K → X} {j : K → Y} (hi : IsOpenEmbedding i) (hj : IsOpenEmbedding j)
  (μ : Measure X) (ν : Measure Y)

omit [CompactSpace K] in
private theorem integral_density_mul_extended_test (q : X → ℂ) (g : SchwartzBruhat K) :
    (∫ x, q x * openEmbeddingTestExtension hi g x ∂μ) = ∫ k, q (i k) * g k ∂(μ.comap i) := by
  calc
    _ = ∫ x in range i, q x * openEmbeddingTestExtension hi g x ∂μ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [openEmbeddingTestExtension_apply_of_not_mem hi g hx, mul_zero]
    _ = _ := by
      rw [← hi.measurableEmbedding.map_comap, hi.measurableEmbedding.integral_map]
      simp only [openEmbeddingTestExtension_apply]

/-- If two open embeddings of a compact chart have equal pulled-back measures and
compare the test evaluations, local density transfers between their images. -/
theorem density_transfer_of_openEmbedding (D : Distribution X) (T : Distribution Y)
    (hMeasure : μ.comap i = ν.comap j)
    (hCompare : ∀ g : SchwartzBruhat K, D (openEmbeddingTestExtension hi g) = T (openEmbeddingTestExtension hj g))
    (θ : X → ℂ) (hθ : LocallyIntegrable θ μ)
    (hD : ∀ f : SchwartzBruhat X, support (f : X → ℂ) ⊆ range i → D f = ∫ x, θ x * f x ∂μ) :
    ∃ η : Y → ℂ, Integrable η ν ∧ ∀ f : SchwartzBruhat Y,
      support (f : Y → ℂ) ⊆ range j → T f = ∫ y, η y * f y ∂ν := by
  let η := j.extend (θ ∘ i) 0
  have hη (k : K) : η (j k) = θ (i k) := hj.injective.extend_apply _ _ k
  have hη₀ {y : Y} (hy : y ∉ range j) : η y = 0 := extend_apply' _ _ _ hy
  have hiC : IsCompact (range i) := isCompact_range hi.continuous
  have hjC : IsCompact (range j) := isCompact_range hj.continuous
  have hjMeas := hj.measurableEmbedding
  have hiMeas := hi.measurableEmbedding
  have hθ' : Integrable (θ ∘ i) (μ.comap i) := by
    apply hiMeas.integrable_map_iff.mp
    rw [hiMeas.map_comap]
    exact hθ.integrableOn_isCompact hiC
  have hηJ : IntegrableOn η (range j) ν := by
    change Integrable η (ν.restrict (range j))
    rw [← hjMeas.map_comap]
    apply hjMeas.integrable_map_iff.mpr
    rw [← hMeasure, show η ∘ j = θ ∘ i from funext hη]
    exact hθ'
  have hηInt : Integrable η ν := by
    have hInd := (integrable_indicator_iff hjC.measurableSet).mpr hηJ
    have hEq : (range j).indicator η = η := by
      funext y
      by_cases hy : y ∈ range j
      · exact indicator_of_mem hy _
      · rw [indicator_of_notMem hy, hη₀ hy]
    rwa [hEq] at hInd
  refine ⟨η, hηInt, fun f hf => ?_⟩
  let g := pullback hj.isEmbedding.toHomeomorph (SchwartzBruhat.restrictClosed hjC.isClosed f)
  have hg : openEmbeddingTestExtension hj g = f := by
    apply Hecke.TestFunction.ext
    intro y
    by_cases hy : y ∈ range j
    · obtain ⟨k, rfl⟩ := hy
      rw [openEmbeddingTestExtension_apply]
      rfl
    · rw [openEmbeddingTestExtension_apply_of_not_mem hj g hy]
      exact (notMem_support.mp (fun h => hy (hf h))).symm
  have hSupp : support (openEmbeddingTestExtension hi g : X → ℂ) ⊆ range i := by
    intro x hx
    by_contra hn
    exact hx (openEmbeddingTestExtension_apply_of_not_mem hi g hn)
  rw [← hg, ← hCompare g, hD _ hSupp,
    integral_density_mul_extended_test hi μ θ g, integral_density_mul_extended_test hj ν η g,
    hMeasure]
  simp only [hη]

end OpenCharts

section Exponential

variable {A K : Type*} [TopologicalSpace A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [CompactSpace K]
  {C : Set A} (hC : IsOpen C) (E : C ≃ₜ K) {j : K → A} (hj : IsOpenEmbedding j)
  (μ : Measure A)

/-- A density on the additive source of a measured exponential chart gives a
locally integrable density in the target coordinates. -/
def ExponentialDensityTransferStatement (D T : Distribution A) : Prop :=
  MeasurePreserving E (μ.comap (Subtype.val : C → A)) (μ.comap j) →
  ExponentialTraceChartAgreement hC E hj D T →
  (∃ θ : A → ℂ, LocallyIntegrable θ μ ∧ ∀ f : SchwartzBruhat A,
    support (f : A → ℂ) ⊆ C → D f = ∫ x, θ x * f x ∂μ) →
  ∃ η : A → ℂ, Integrable η μ ∧ ∀ f : SchwartzBruhat A,
    support (f : A → ℂ) ⊆ range j → T f = ∫ y, η y * f y ∂μ

set_option maxHeartbeats 1400000 in
theorem exponentialDensityTransfer (D T : Distribution A) :
    ExponentialDensityTransferStatement hC E hj μ D T := by
  rintro hMeasure hCompare ⟨θ, hθ, hD⟩
  let v : C → A := Subtype.val
  let i : K → A := v ∘ E.symm
  have hi : IsOpenEmbedding i := hC.isOpenEmbedding_subtypeVal.comp E.symm.isOpenEmbedding
  have hRange : range i ⊆ C := fun _ ⟨k, hk⟩ => hk ▸ (E.symm k).property
  have hComap : μ.comap i = μ.comap j := by
    have hv := hC.isOpenEmbedding_subtypeVal.measurableEmbedding
    have he := E.symm.toMeasurableEquiv.measurableEmbedding
    change μ.comap (v ∘ E.symm) = μ.comap j
    rw [← Measure.comap_comap (f := E.symm) (g := v) (fun _ hs => he.measurableSet_image.mpr hs)
      hv.injective (fun _ hs => hv.measurableSet_image.mpr hs)]
    change (μ.comap v).comap E.toMeasurableEquiv.symm = μ.comap j
    rw [E.toMeasurableEquiv.comap_symm]
    exact hMeasure.map_eq
  exact density_transfer_of_openEmbedding hi hj μ μ D T hComap hCompare θ hθ (fun f hf => hD f (hf.trans hRange))

end Exponential

end Langlands.BaseChange
