import Langlands.Analysis.Local.HaarInversionDensityStatement
import Langlands.Analysis.Local.ModularCharacterContinuity
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLDensity

noncomputable section

namespace Langlands.Haar

open MeasureTheory MeasureTheory.Measure Set
open scoped NNReal ENNReal Topology

universe uG

private theorem density_smul_nnreal {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (c : ℝ≥0) (w : X → ℝ≥0∞) :
    (c • μ).withDensity w = (c : ℝ≥0∞) • μ.withDensity w := by
  exact withDensity_smul_measure (c : ℝ≥0∞) w

private theorem inv_smul_nnreal {G : Type*} [Group G]
    [MeasurableSpace G] [MeasurableInv G] (μ : Measure G) (c : ℝ≥0) :
    (c • μ).inv = c • μ.inv := by
  exact Measure.map_smul _ measurable_inv.aemeasurable

/-- The positive modular density gives the actual inverse Haar measure. -/
theorem haarInversionDensity : HaarInversionDensityStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _
  let w : G → ℝ≥0∞ := fun x => modularCharacter x
  have hw : Measurable w :=
    (ENNReal.continuous_coe.comp continuous_modularCharacter_of_locallyCompact).measurable
  have hwi : Measurable (fun x : G => w x⁻¹) := hw.comp measurable_inv
  have hwprod (x : G) : w x⁻¹ * w x = 1 := by
    simp only [w, ← ENNReal.coe_mul, ← map_mul, inv_mul_cancel, map_one, ENNReal.coe_one]
  let ν := μ.withDensity w
  let : IsLocallyFiniteMeasure ν :=
    IsLocallyFiniteMeasure.withDensity_coe continuous_modularCharacter_of_locallyCompact
  have hνmap (g : G) : ν.map (· * g) = ν := by
    have hmap : μ.map (· * g) = modularCharacter g • μ :=
      map_right_mul_eq_modularCharacterFun_smul μ g
    change (μ.withDensity w).map (Homeomorph.mulRight g).toMeasurableEquiv = _
    rw [Langlands.RankinSelberg.GLDeterminantDensity.map_withDensity_equiv]
    change (μ.map (· * g)).withDensity (fun x => w (x * g⁻¹)) = _
    rw [hmap, density_smul_nnreal]
    rw [← withDensity_smul (modularCharacter g : ℝ≥0∞) (by fun_prop)]
    congr 1
    funext x
    change w g * w (x * g⁻¹) = w x
    simp only [w, map_mul, ENNReal.coe_mul]
    calc
      _ = (modularCharacter x : ℝ≥0∞) *
          ((modularCharacter g⁻¹ : ℝ≥0∞) * (modularCharacter g : ℝ≥0∞)) := by ring
      _ = _ := by rw [hwprod]; simp
  let : IsMulRightInvariant ν := ⟨hνmap⟩
  let c : ℝ≥0 := haarScalarFactor ν.inv μ
  have hc : ν.inv = c • μ := isMulLeftInvariant_eq_smul ν.inv μ
  have hνinv : ν.inv = μ.inv.withDensity (fun x => w x⁻¹) := by
    change (μ.withDensity w).map (MeasurableEquiv.inv G) = _
    exact Langlands.RankinSelberg.GLDeterminantDensity.map_withDensity_equiv μ (MeasurableEquiv.inv G) w
  have hcancel : ν.inv.withDensity w = μ.inv := by
    rw [hνinv, ← withDensity_mul μ.inv hwi hw]
    have heq : (fun x => w x⁻¹) * w = 1 := by
      funext x
      exact hwprod x
    rw [heq, withDensity_one]
  have hi : μ.inv = c • ν := by
    rw [← hcancel, hc, density_smul_nnreal]
    rfl
  have hback : ν = c • μ.inv := by
    simpa only [inv_smul_nnreal, Measure.inv_inv] using
      congrArg (fun η : Measure G => η.inv) hc
  have hsq : μ.inv = (c * c) • μ.inv := by
    calc
      μ.inv = c • ν := hi
      _ = c • (c • μ.inv) := congrArg (fun η : Measure G => c • η) hback
      _ = _ := by rw [smul_smul]
  have hsqμ : μ = (c * c) • μ := by
    simpa only [inv_smul_nnreal, Measure.inv_inv] using
      congrArg (fun η : Measure G => η.inv) hsq
  let K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have hmul : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K := by
    conv_rhs => rw [hsqμ]
    simp
  have hcc : c * c = 1 := by
    apply ENNReal.coe_injective
    exact (ENNReal.mul_left_inj
      (measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
      K.isCompact.measure_lt_top.ne).1 hmul
  have hc1 : c = 1 := by
    apply NNReal.coe_injective
    have hccR : (c : ℝ) * (c : ℝ) = 1 := by exact_mod_cast hcc
    change (c : ℝ) = 1
    nlinarith [c.coe_nonneg]
  have hleft : μ.inv = ν := by simpa [hc1] using hi
  refine ⟨hleft, ?_⟩
  change μ = μ.inv.withDensity (fun x => w x⁻¹)
  rw [hleft]
  change μ = (μ.withDensity w).withDensity (fun x => w x⁻¹)
  rw [← withDensity_mul μ hw hwi]
  have heq : w * (fun x => w x⁻¹) = 1 := by
    funext x
    change w x * w x⁻¹ = 1
    simpa only [mul_comm] using hwprod x
  rw [heq, withDensity_one]

end Langlands.Haar
