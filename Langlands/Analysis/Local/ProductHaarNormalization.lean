import Langlands.Analysis.Local.QuotientMeasureEquiv
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Haar normalization with a prescribed direct factor -/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure Set Topology
open scoped NNReal

section Factors

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]
  [TopologicalSpace G₁] [TopologicalSpace G₂]
  [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
  [MeasurableSpace G₁] [BorelSpace G₁] [MeasurableSpace G₂] [BorelSpace G₂]
  [SecondCountableTopology G₁] [SecondCountableTopology G₂]
  [LocallyCompactSpace G₁] [T2Space G₁]

omit [SecondCountableTopology G₁] in
private theorem isMulRightInvariant_second_factor
    (μ₁ : Measure G₁) [IsHaarMeasure μ₁] (μ₂ : Measure G₂) [SFinite μ₂]
    [IsMulRightInvariant (μ₁.prod μ₂)] : IsMulRightInvariant μ₂ := by
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds (1 : G₁)
  have hK₀ := (measure_pos_of_mem_nhds μ₁ hKn).ne'
  have hKtop := (hKc.measure_lt_top (μ := μ₁)).ne
  refine ⟨fun y => ?_⟩
  ext s hs
  let R : G₁ × G₂ → G₁ × G₂ := fun p => p * (1, y)
  let r : G₂ → G₂ := fun z => z * y
  have hR : Measurable R := measurable_mul_const (1, y)
  have hr : Measurable r := measurable_mul_const y
  have hpre : R ⁻¹' (K ×ˢ s) = K ×ˢ (r ⁻¹' s) := by
    ext p
    simp [R, r]
  have hmap : Measure.map R (μ₁.prod μ₂) = μ₁.prod μ₂ :=
    map_mul_right_eq_self (μ₁.prod μ₂) (1, y)
  have hval := congrArg (fun m : Measure (G₁ × G₂) => m (K ×ˢ s)) hmap
  change (Measure.map R (μ₁.prod μ₂)) (K ×ˢ s) = (μ₁.prod μ₂) (K ×ˢ s) at hval
  rw [Measure.map_apply hR (hKc.measurableSet.prod hs), hpre,
    Measure.prod_prod, Measure.prod_prod] at hval
  rw [Measure.map_apply hr hs]
  exact (ENNReal.mul_left_inj hK₀ hKtop).mp (by
    simpa only [mul_comm (μ₁ K)] using hval)

end Factors

section Normalization

variable {G₁ G₂ G : Type*} [Group G₁] [Group G₂] [Group G]
  [TopologicalSpace G₁] [TopologicalSpace G₂] [TopologicalSpace G]
  [MeasurableSpace G₁] [MeasurableSpace G₂] [MeasurableSpace G]
  (D : G₁ × G₂ ≃ₜ* G) (μ₁ : Measure G₁) (μ : Measure G)

/-- The complementary factor has an exact normalization for a prescribed
local Haar measure and right-invariant ambient Haar measure. -/
def ProductHaarNormalizationStatement : Prop :=
  ∀ [IsTopologicalGroup G₁] [IsTopologicalGroup G₂] [IsTopologicalGroup G]
    [BorelSpace G₁] [BorelSpace G₂] [BorelSpace G]
    [SecondCountableTopology G₁] [SecondCountableTopology G₂]
    [LocallyCompactSpace G₁] [LocallyCompactSpace G₂] [T2Space G₁],
    IsHaarMeasure μ₁ → IsHaarMeasure μ → IsMulRightInvariant μ →
    ∃ μ₂ : Measure G₂, IsHaarMeasure μ₂ ∧ μ₂.Regular ∧ IsMulRightInvariant μ₂ ∧
      Measure.map D (μ₁.prod μ₂) = μ

theorem productHaarNormalization : ProductHaarNormalizationStatement D μ₁ μ := by
  intro _ _ _ _ _ _ _ _ _ _ _ h₁ hμ hright
  let := h₁
  let := hμ
  let := hright
  let μpull := Measure.map D.symm μ
  let μ₂₀ : Measure G₂ := Measure.haar
  let : IsHaarMeasure μpull := D.symm.isHaarMeasure_map μ
  let : IsMulRightInvariant μpull := isMulRightInvariant_map D.symm μ
  let c := haarScalarFactor μpull (μ₁.prod μ₂₀)
  have hmul : μpull = c • (μ₁.prod μ₂₀) :=
    isMulLeftInvariant_eq_smul μpull (μ₁.prod μ₂₀)
  have hc : c ≠ 0 := by
    intro hz
    exact (NeZero.ne μpull) (by simpa only [hz, zero_smul] using hmul)
  let μ₂ := c • μ₂₀
  let : IsHaarMeasure μ₂ := IsHaarMeasure.nnreal_smul μ₂₀ hc
  have hprod : μ₁.prod μ₂ = μpull := by
    change μ₁.prod (c • μ₂₀) = μpull
    rw [Measure.prod_smul_right, ← hmul]
  have hrightProd : IsMulRightInvariant (μ₁.prod μ₂) := hprod ▸ inferInstanceAs
    (IsMulRightInvariant μpull)
  refine ⟨μ₂, inferInstance, inferInstance, isMulRightInvariant_second_factor μ₁ μ₂, ?_⟩
  rw [hprod]
  exact MeasurableEquiv.map_map_symm D.toHomeomorph.toMeasurableEquiv

end Normalization

end Langlands.QuotientIntegration
