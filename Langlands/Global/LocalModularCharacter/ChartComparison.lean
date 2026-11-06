import Langlands.Global.LocalModularCharacter.ComparisonMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-! # Bounding the modular character through a chart at the identity

A chart `φ` of a locally compact group `H` at `1`, with values in a proper normed additive group
`E` carrying an additive Haar measure `λ`, transports `λ` to a finite measure on `H`.  Two
estimates in the chart, one for left translations by elements near `1` and one for conjugation
by a fixed element `g`, make this measure satisfy the hypotheses of
`modularCharacter_le_of_comparison`. -/

noncomputable section

open MeasureTheory Measure Filter Topology Set Metric
open scoped NNReal ENNReal

namespace Langlands.Global.LocalModularCharacter

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
variable (l : Measure E) [IsAddHaarMeasure l] (φ : OpenPartialHomeomorph H E)

/-- The additive Haar measure on the ball of radius `R` around `0`, transported to `H` by the
inverse of the chart. -/
def chartMeasure (R : ℝ) : Measure H :=
  (l.restrict (ball (0 : E) R)).map φ.symm

omit [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H]
  [IsAddHaarMeasure l] [Group H] [ProperSpace E] in
theorem chartMeasure_apply {R : ℝ} (hR : ball (0 : E) R ⊆ φ.target) {S : Set H}
    (hS : MeasurableSet S) :
    chartMeasure l φ R S = l (φ '' (φ.source ∩ S) ∩ ball 0 R) := by
  have hae : AEMeasurable φ.symm (l.restrict (ball (0 : E) R)) :=
    (φ.continuousOn_symm.mono hR).aemeasurable measurableSet_ball
  rw [chartMeasure, map_apply_of_aemeasurable hae hS, Measure.restrict_apply' measurableSet_ball,
    φ.image_source_inter_eq', inter_assoc, inter_eq_right.2 (inter_subset_right.trans hR)]

omit [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H]
  [Group H] in
instance isFiniteMeasure_chartMeasure (R : ℝ) : IsFiniteMeasure (chartMeasure l φ R) := by
  have : IsFiniteMeasure (l.restrict (ball (0 : E) R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  unfold chartMeasure
  infer_instance

/-- **Modular character through a chart.**  Let `φ` be a chart of `H` at `1` with `φ 1 = 0`.
Suppose that left translation by points near `1`, read in the chart, increases the Haar measure
of subsets of small balls by at most `1 + η`, and that conjugation by `g`, read in the chart,
sends small balls `B` to sets of measure at most `(1 + η) D λ(B)`.  Then the modular character
of `g` is at most `D`. -/
theorem modularCharacter_le_of_chart (h1 : (1 : H) ∈ φ.source) (h0 : φ 1 = 0) (g : H)
    (D : ℝ≥0)
    (hP1 : ∀ η : ℝ≥0, 0 < η → ∃ r > 0, ∀ y ∈ ball (0 : E) r, ∀ X ⊆ ball (0 : E) r,
      l ((fun z => φ (φ.symm y * φ.symm z)) '' X) ≤ (1 + η) * l X)
    (hP2 : ∀ η : ℝ≥0, 0 < η → ∃ r₀ > 0, ∀ r ≤ r₀,
      l ((fun z => φ (g * φ.symm z * g⁻¹)) '' ball 0 r) ≤ (1 + η) * D * l (ball 0 r)) :
    modularCharacter g ≤ D := by
  have h0t : (0 : E) ∈ φ.target := h0 ▸ φ.map_source h1
  obtain ⟨R, hR, hRt⟩ := Metric.isOpen_iff.1 φ.open_target 0 h0t
  refine modularCharacter_le_of_comparison (chartMeasure l φ R) g D ?_ ?_ ?_
  · intro U hU
    obtain ⟨U', hU'U, hU'o, h1U'⟩ := mem_nhds_iff.1 hU
    have hopen : IsOpen (φ '' (φ.source ∩ U') ∩ ball 0 R) :=
      (φ.isOpen_image_source_inter hU'o).inter isOpen_ball
    have hmem : (0 : E) ∈ φ '' (φ.source ∩ U') ∩ ball 0 R :=
      ⟨⟨1, ⟨h1, h1U'⟩, h0⟩, mem_ball_self hR⟩
    calc 0 < l (φ '' (φ.source ∩ U') ∩ ball 0 R) := hopen.measure_pos l ⟨0, hmem⟩
      _ = chartMeasure l φ R U' := (chartMeasure_apply l φ hRt hU'o.measurableSet).symm
      _ ≤ chartMeasure l φ R U := measure_mono hU'U
  · intro η hη
    obtain ⟨r, hr, hP⟩ := hP1 η hη
    have hr' : 0 < min r R := lt_min hr hR
    refine ⟨φ.source ∩ φ ⁻¹' ball 0 (min r R),
      (φ.isOpen_inter_preimage isOpen_ball).mem_nhds ⟨h1, by simp [h0, hr']⟩, ?_⟩
    rintro x ⟨hxs, hxb⟩ T hT hTm
    have hxT : MeasurableSet ((x * ·) '' T) :=
      (MeasurableEquiv.mulLeft x).measurableSet_image.2 hTm
    have hTs : φ.source ∩ T = T := inter_eq_right.2 fun t ht => (hT ht).1
    have hXr : φ '' T ⊆ ball 0 (min r R) := by
      rintro _ ⟨t, ht, rfl⟩
      exact (hT ht).2
    calc chartMeasure l φ R ((x * ·) '' T)
        = l (φ '' (φ.source ∩ (x * ·) '' T) ∩ ball 0 R) := chartMeasure_apply l φ hRt hxT
      _ ≤ l ((fun z => φ (φ.symm (φ x) * φ.symm z)) '' (φ '' T)) := by
          apply measure_mono
          rintro _ ⟨⟨_, ⟨-, t, ht, rfl⟩, rfl⟩, -⟩
          exact ⟨φ t, ⟨t, ht, rfl⟩, by simp only [φ.left_inv hxs, φ.left_inv (hT ht).1]⟩
      _ ≤ (1 + η) * l (φ '' T) :=
          hP (φ x) (ball_subset_ball (min_le_left _ _) hxb) _
            (hXr.trans (ball_subset_ball (min_le_left _ _)))
      _ = (1 + η) * chartMeasure l φ R T := by
          rw [chartMeasure_apply l φ hRt hTm, hTs,
            inter_eq_left.2 (hXr.trans (ball_subset_ball (min_le_right _ _)))]
  · intro η hη U hU
    obtain ⟨r₀, hr₀, hP⟩ := hP2 η hη
    have himg : φ '' (φ.source ∩ U) ∈ 𝓝 (0 : E) :=
      h0 ▸ φ.image_mem_nhds h1 (inter_mem (φ.open_source.mem_nhds h1) hU)
    obtain ⟨r₁, hr₁, hr₁U⟩ := Metric.mem_nhds_iff.1 himg
    have hr : 0 < min (min r₀ R) r₁ := lt_min (lt_min hr₀ hR) hr₁
    have hrR : ball (0 : E) (min (min r₀ R) r₁) ⊆ ball 0 R :=
      ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))
    have hrt : ball (0 : E) (min (min r₀ R) r₁) ⊆ φ.target := hrR.trans hRt
    have hVo : IsOpen (φ.source ∩ φ ⁻¹' ball 0 (min (min r₀ R) r₁)) :=
      φ.isOpen_inter_preimage isOpen_ball
    refine ⟨φ.source ∩ φ ⁻¹' ball 0 (min (min r₀ R) r₁), ?_, hVo, ⟨h1, by simp [h0, hr]⟩, ?_⟩
    · rintro v ⟨hvs, hvb⟩
      obtain ⟨u, ⟨hus, huU⟩, hu⟩ := hr₁U (ball_subset_ball (min_le_right _ _) hvb)
      rwa [← φ.injOn hus hvs hu]
    · have hgVo : IsOpen ((fun x => g * x * g⁻¹) ''
          (φ.source ∩ φ ⁻¹' ball 0 (min (min r₀ R) r₁))) :=
        ((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)).isOpenMap _ hVo
      have hball : l (ball 0 (min (min r₀ R) r₁)) ≤
          chartMeasure l φ R (φ.source ∩ φ ⁻¹' ball 0 (min (min r₀ R) r₁)) := by
        rw [chartMeasure_apply l φ hRt hVo.measurableSet]
        apply measure_mono
        intro z hz
        refine ⟨⟨φ.symm z, ⟨φ.map_target (hrt hz), φ.map_target (hrt hz), ?_⟩,
          φ.right_inv (hrt hz)⟩, hrR hz⟩
        rw [mem_preimage, φ.right_inv (hrt hz)]
        exact hz
      calc chartMeasure l φ R ((fun x => g * x * g⁻¹) ''
            (φ.source ∩ φ ⁻¹' ball 0 (min (min r₀ R) r₁)))
          = l (φ '' (φ.source ∩ (fun x => g * x * g⁻¹) ''
              (φ.source ∩ φ ⁻¹' ball 0 (min (min r₀ R) r₁))) ∩ ball 0 R) :=
            chartMeasure_apply l φ hRt hgVo.measurableSet
        _ ≤ l ((fun z => φ (g * φ.symm z * g⁻¹)) '' ball 0 (min (min r₀ R) r₁)) := by
            apply measure_mono
            rintro _ ⟨⟨_, ⟨-, v, ⟨hvs, hvb⟩, rfl⟩, rfl⟩, -⟩
            exact ⟨φ v, hvb, by simp only [φ.left_inv hvs]⟩
        _ ≤ (1 + η) * D * l (ball 0 (min (min r₀ R) r₁)) :=
            hP _ ((min_le_left _ _).trans (min_le_left _ _))
        _ ≤ (1 + η) * D * chartMeasure l φ R (φ.source ∩ φ ⁻¹' ball 0 (min (min r₀ R) r₁)) := by
            gcongr

end Langlands.Global.LocalModularCharacter
