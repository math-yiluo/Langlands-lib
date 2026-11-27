import Langlands.HarmonicAnalysis.UnitConjugation.ExponentialBall
import Langlands.HarmonicAnalysis.UnitConjugation.NormCongruence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Exponential coordinates and Haar measure on small congruence subgroups -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open MeasureTheory MeasureTheory.Measure Metric Set Function _root_.Topology
open scoped NNReal

variable {A : Type*} [NormedRing A] [IsUltrametricDist A]

/-- The additive coordinate `u − 1` on the norm-unit congruence subgroup. -/
def normUnitCoordinate {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (u : normUnitCongruence (R := A) hr₀ hr₁) : A := (u.val : A) - 1

variable [ProperSpace A]

private theorem isOpenEmbedding_normUnitCoordinate {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    IsOpenEmbedding (normUnitCoordinate (A := A) hr₀.le hr₁) :=
  ((Homeomorph.subRight (1 : A)).isOpenEmbedding.comp Units.isOpenEmbedding_val).comp
    (isOpen_normUnitCongruence (R := A) hr₀ hr₁).isOpenEmbedding_subtypeVal

private theorem range_normUnitCoordinate {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    range (normUnitCoordinate (A := A) hr₀ hr₁) = closedBall 0 r := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    exact u.property
  · intro hx
    have hnorm : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hx
    let u : Aˣ := Units.oneSub (-x) (by simpa only [norm_neg] using (hnorm.trans_lt hr₁))
    have hu : (u : A) - 1 = x := by simp [u, Units.val_oneSub, add_comm]
    exact ⟨⟨u, (mem_normUnitCongruence hr₀ hr₁ u).mpr (hu.symm ▸ hnorm)⟩, hu⟩

variable [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]

private theorem normUnitCoordinate_haar {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1)
    (μ : Measure A) [μ.IsAddHaarMeasure] :
    (μ.comap (normUnitCoordinate hr₀.le hr₁)).IsHaarMeasure := by
  let K := normUnitCongruence (R := A) hr₀.le hr₁
  let j := normUnitCoordinate (A := A) hr₀.le hr₁
  let ν := μ.comap j
  have hj := isOpenEmbedding_normUnitCoordinate (A := A) hr₀ hr₁
  have hJ := hj.measurableEmbedding
  have hS : Measure.map j ν = μ.restrict (closedBall 0 r) := by
    rw [hJ.map_comap, range_normUnitCoordinate]
  refine { toIsFiniteMeasureOnCompacts := IsFiniteMeasureOnCompacts.comap' μ hj.continuous hJ
           toIsOpenPosMeasure := IsOpenPosMeasure.comap μ hj
           map_mul_left_eq_self := fun k => ?_ }
  let b : A := (k.val : A) - 1
  let u (x : A) := b * x + b
  let c : ℝ≥0 := ⟨r, hr₀.le⟩
  have huc : Continuous u := (continuous_const.mul continuous_id).add continuous_const
  have hLip : LipschitzOnWith c u (closedBall 0 r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x _ y _
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : u x - u y = b * (x - y) := by simp [u, mul_sub]
    rw [hsub]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (show ‖b‖ ≤ r from k.property) (norm_nonneg _))
  have hb : b ∈ closedBall (0 : A) r := by
    rw [mem_closedBall, dist_zero_right]
    exact k.property
  have hU : Measure.map (fun x => x + u x) (μ.restrict (closedBall 0 r)) =
      μ.restrict (closedBall 0 r) := by
    have hc : c < 1 := hr₁
    have h := map_closedBall_add_perturbation μ (0 : A) hr₀.le hLip hc huc
    simpa only [u, mul_zero, zero_add, ← IsUltrametricDist.closedBall_eq_of_mem hb] using h
  have hfun : j ∘ (k * · : K → K) = (fun x => x + u x) ∘ j := by
    funext v
    change (k.val : A) * (v.val : A) - 1 = (v.val : A) - 1 + (b * ((v.val : A) - 1) + b)
    dsimp only [b]
    noncomm_ring
  have hm : Measurable (fun x : A => x + u x) := (continuous_id.add huc).measurable
  apply hJ.map_injective
  rw [Measure.map_map hJ.measurable (measurable_const_mul k), hfun,
    ← Measure.map_map hm hJ.measurable, hS]
  exact hU

/-- The small exponential chart takes additive Haar on the ball to left Haar
on the unit subgroup in the `u − 1` normalization. -/
def ExponentialCongruenceHaarStatement (F A : Type*) [NontriviallyNormedField F] [CharZero F]
    [IsUltrametricDist F] [NormedRing A] [NormedAlgebra F A] [IsUltrametricDist A] [ProperSpace A]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace Aˣ] [BorelSpace Aˣ] : Prop :=
  ∃ ε > (0 : ℝ), ∀ (r : ℝ) (hr₀ : 0 < r) (hr₁ : r < 1), r ≤ ε →
    let K := normUnitCongruence (R := A) hr₀.le hr₁
    let S := closedBall (0 : A) r
    ∃ E : S ≃ₜ K, (∀ x, ((E x).val : A) = NormedSpace.exp (x : A)) ∧
      ∀ (μ : Measure A) [μ.IsAddHaarMeasure],
        let ν := μ.comap (normUnitCoordinate hr₀.le hr₁)
        ν.IsHaarMeasure ∧ MeasurePreserving E (μ.comap (Subtype.val : S → A)) ν

variable {F : Type*} [NontriviallyNormedField F] [CharZero F] [IsUltrametricDist F] [NormedAlgebra F A]

theorem exponentialCongruenceHaar : ExponentialCongruenceHaarStatement F A := by
  obtain ⟨ε, hε, he⟩ := exponentialBallTransport (F := F) (A := A)
  refine ⟨ε, hε, fun r hr₀ hr₁ hr => ?_⟩
  obtain ⟨e, he, hmeasure⟩ := he r hr₀ hr
  let K := normUnitCongruence (R := A) hr₀.le hr₁
  let S := closedBall (0 : A) r
  let j := normUnitCoordinate (A := A) hr₀.le hr₁
  have hj := isOpenEmbedding_normUnitCoordinate (A := A) hr₀ hr₁
  let J : K ≃ₜ S := hj.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr (range_normUnitCoordinate hr₀.le hr₁))
  let E := e.toHomeomorph.trans J.symm
  have hEval (x : S) : j (E x) = NormedSpace.exp (x : A) - 1 := by
    change ((J (J.symm (e x))) : A) = _
    rw [J.apply_symm_apply]
    exact he x
  refine ⟨E, fun x => ?_, ?_⟩
  · have h := congrArg (fun a : A => a + 1) (hEval x)
    simpa only [j, normUnitCoordinate, sub_add_cancel] using h
  intro μ _
  let ν := μ.comap j
  refine ⟨normUnitCoordinate_haar hr₀ hr₁ μ, ⟨E.continuous.measurable, ?_⟩⟩
  let v : S → A := Subtype.val
  let f (x : A) := NormedSpace.exp x - 1
  have hv := MeasurableEmbedding.subtype_coe (s := S) isClosed_closedBall.measurableSet
  have hJ := hj.measurableEmbedding
  have hvmap : Measure.map v (μ.comap v) = μ.restrict S := by rw [hv.map_comap, Subtype.range_coe]
  have hf : AEMeasurable f (μ.restrict S) := by
    apply ContinuousOn.aemeasurable _ isClosed_closedBall.measurableSet
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact ((hj.continuous.comp E.continuous).congr hEval)
  have hfun : j ∘ E = f ∘ v := funext hEval
  apply hJ.map_injective
  rw [Measure.map_map hJ.measurable E.continuous.measurable, hfun,
    ← AEMeasurable.map_map_of_aemeasurable (hvmap.symm ▸ hf) hv.measurable.aemeasurable,
    hvmap, hmeasure μ, hJ.map_comap, range_normUnitCoordinate]

end Langlands.HarmonicAnalysis.UnitConjugation
