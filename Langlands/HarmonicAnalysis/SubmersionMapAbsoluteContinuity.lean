import Langlands.HarmonicAnalysis.CompactSubmersionPushforward
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.Topology.Compactness.Lindelof

/-!
# Absolute continuity on the submersion locus

A continuous map between finite-dimensional spaces over a nonarchimedean local field
pushes forward Haar measure restricted to an open submersion locus to a measure absolutely
continuous with respect to target Haar measure. The proof applies the compact submersion
pushforward theorem on a countable cover by compact open balls.
-/

namespace Langlands.HarmonicAnalysis

open Filter Function MeasureTheory Metric Set Topology
open scoped ENNReal NNReal

/-- Absolute continuity of the pushforward of additive Haar measure restricted to an open
set on which the map is strictly differentiable with surjective derivative. -/
def SubmersionMapAbsoluteContinuityStatement.{u, v, w} : Prop :=
  ∀ (F : Type u) [NontriviallyNormedField F] [ProperSpace F]
    (X : Type v) [NormedAddCommGroup X] [NormedSpace F X] [FiniteDimensional F X]
    [IsUltrametricDist X] [MeasurableSpace X] [BorelSpace X]
    (Y : Type w) [NormedAddCommGroup Y] [NormedSpace F Y] [FiniteDimensional F Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [μ.IsAddHaarMeasure] (ν : Measure Y) [ν.IsAddHaarMeasure]
    (Φ : X → Y) (U : Set X), Continuous Φ → IsOpen U →
    (∀ x ∈ U, ∃ D : X →L[F] Y, HasStrictFDerivAt Φ D x ∧ Surjective D) →
    Measure.map Φ (μ.restrict U) ≪ ν

/-- Apply `compactSubmersionPushforward` to the indicators of compact open balls in `U`. -/
theorem submersionMapAbsoluteContinuity : SubmersionMapAbsoluteContinuityStatement.{u, v, w} := by
  classical
  intro F _ _ X _ _ _ _ _ _ Y _ _ _ _ _ μ _ ν _ Φ U hΦ hU hDeriv
  have : ProperSpace X := FiniteDimensional.proper F X
  have hlocal (x : U) : ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
      Measure.map Φ (μ.restrict V) ≪ ν := by
    obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds x.property)
    let V := closedBall (x : X) (r / 2)
    have hV : IsClopen V := IsUltrametricDist.isClopen_closedBall _ (half_pos hr).ne'
    have hVU : V ⊆ U := (closedBall_subset_ball (half_lt_self hr)).trans hsub
    let f := (LocallyConstant.const X (1 : ℝ≥0)).indicator hV
    have hSupport : tsupport (f : X → ℝ≥0) ⊆ V := by
      apply closure_minimal _ hV.1
      intro z hz
      by_contra hn
      exact (mem_support.mp hz) (LocallyConstant.indicator_of_notMem _ hV hn)
    have hWeight : μ.withDensity (fun z => (f z : ℝ≥0∞)) = μ.restrict V := by
      have hEq : (fun z => (f z : ℝ≥0∞)) = V.indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext z
        by_cases hz : z ∈ V
        · rw [indicator_of_mem hz, LocallyConstant.indicator_of_mem _ _ hz]
          simp
        · rw [indicator_of_notMem hz, LocallyConstant.indicator_of_notMem _ _ hz]
          simp
      rw [hEq, withDensity_indicator hV.2.measurableSet]
      exact withDensity_one
    have hDeriv' (z : X) (hz : z ∈ tsupport (f : X → ℝ≥0)) :
        ∃ D : F × X →L[F] Y, HasStrictFDerivAt (Φ ∘ Prod.snd) D (0, z) ∧
          Surjective (D.comp (ContinuousLinearMap.inr F F X)) := by
      obtain ⟨D, hD, hs⟩ := hDeriv z (hVU (hSupport hz))
      refine ⟨D.comp (ContinuousLinearMap.snd F F X), ?_, hs⟩
      have hSnd : HasStrictFDerivAt (@Prod.snd F X) (ContinuousLinearMap.snd F F X)
          ((0 : F), z) := hasStrictFDerivAt_snd
      exact HasStrictFDerivAt.comp ((0 : F), z) (f := Prod.snd) hD hSnd
    obtain ⟨U', _, hZero, g, _, hMap⟩ :=
      compactSubmersionPushforward F F X Y μ ν (Φ ∘ Prod.snd) 0 f
        (hΦ.comp continuous_snd)
        ((isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hSupport)
        hDeriv'
    have hAC : Measure.map Φ (μ.restrict V) ≪ ν := by
      rw [← hWeight, show Measure.map Φ (μ.withDensity (fun z => f z)) = _ from hMap 0 hZero]
      exact withDensity_absolutelyContinuous ν _
    exact ⟨V, hV.2, mem_closedBall_self (half_pos hr).le, hAC⟩
  choose V hOpen hMem hAC using hlocal
  obtain ⟨C, hC, hCover⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
    V hOpen fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hMem ⟨x, hx⟩⟩
  apply Measure.AbsolutelyContinuous.mk
  intro s hMeas hs
  have hPre := hΦ.measurable hMeas
  rw [Measure.map_apply hΦ.measurable hMeas, Measure.restrict_apply hPre]
  apply measure_mono_null
    (show Φ ⁻¹' s ∩ U ⊆ ⋃ i ∈ C, Φ ⁻¹' s ∩ V i from by
      simpa only [inter_iUnion] using inter_subset_inter_right (Φ ⁻¹' s) hCover)
  apply (measure_biUnion_null_iff hC).mpr
  intro i _
  simpa only [Measure.map_apply hΦ.measurable hMeas, Measure.restrict_apply hPre]
    using hAC i hs

end Langlands.HarmonicAnalysis
