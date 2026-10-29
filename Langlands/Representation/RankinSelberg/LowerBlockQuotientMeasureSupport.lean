import Langlands.Representation.RankinSelberg.LowerBlockQuotientDisintegrationStatement
import Langlands.Group.GL.CountabilityProof

/-!
# Measure support for lower-block quotient disintegration

Right Haar measure on the actual lower triangular group, positive finite
compact open volumes, and integral transfer from a positive scaled pushforward.
These results do not assert the lower-block measure identity.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Langlands.GeneralLinear

universe u

/-- The actual lower triangular subgroup is closed in the matrix unit group. -/
theorem lowerTriangularSubgroup_isClosed {R : Type u} [CommRing R]
    [TopologicalSpace R] [T2Space R] (d : ℕ) :
    IsClosed (lowerTriangularSubgroup d R : Set (Langlands.GeneralLinear d R)) :=
  isClosed_setOfPred_blockTriangular.preimage Units.continuous_val

end Langlands.GeneralLinear

namespace Langlands.RankinSelberg

open HarmonicAnalysis GeneralLinear

universe uF

section RightHaar

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Inversion sends a left Haar measure to a right Haar measure on the actual
lower triangular group, with no normalization imposed. -/
def lowerTriangularRightHaar (d : ℕ) :
    letI := T.topology
    letI := borel (lowerTriangularSubgroup d F.Carrier)
    Measure (lowerTriangularSubgroup d F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace d
  let : LocallyCompactSpace (lowerTriangularSubgroup d F.Carrier) :=
    (lowerTriangularSubgroup_isClosed d).locallyCompactSpace
  let := borel (lowerTriangularSubgroup d F.Carrier)
  have : BorelSpace (lowerTriangularSubgroup d F.Carrier) := ⟨rfl⟩
  exact (Measure.haar : Measure (lowerTriangularSubgroup d F.Carrier)).inv

/-- All regularity, finiteness and right-invariance properties required of the
triangular measure in lower-block disintegration. -/
theorem lowerTriangularRightHaar_properties (d : ℕ) :
    letI := T.topology
    letI := borel (lowerTriangularSubgroup d F.Carrier)
    let ρ := lowerTriangularRightHaar F T d
    ρ.Regular ∧ SigmaFinite ρ ∧ ρ.IsOpenPosMeasure ∧ IsFiniteMeasureOnCompacts ρ ∧
      ρ.IsMulRightInvariant ∧
      (∀ K : OpenSubgroup (lowerTriangularSubgroup d F.Carrier),
        IsCompact (K : Set (lowerTriangularSubgroup d F.Carrier)) →
          0 < ρ K ∧ ρ K < ∞) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace d
  let := T.generalLinearSecondCountableTopology d
  let : SecondCountableTopology (lowerTriangularSubgroup d F.Carrier) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : LocallyCompactSpace (lowerTriangularSubgroup d F.Carrier) :=
    (lowerTriangularSubgroup_isClosed d).locallyCompactSpace
  let := borel (lowerTriangularSubgroup d F.Carrier)
  have : BorelSpace (lowerTriangularSubgroup d F.Carrier) := ⟨rfl⟩
  dsimp only [lowerTriangularRightHaar]
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro K hK
  exact ⟨K.isOpen.measure_pos _ ⟨1, K.one_mem⟩, hK.measure_lt_top⟩

end RightHaar

/-- Every compact open additive parameter subgroup has positive finite volume
for every supplied scalar Haar measure. -/
theorem rectangularMeasure_compactOpen_pos_lt_top {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (d a : ℕ) :
    letI := T.topology
    letI := borel F.Carrier
    ∀ η : AdditiveHaarMeasure F.Carrier,
      ∀ K : OpenAddSubgroup (Matrix (Fin d) (Fin a) F.Carrier),
        IsCompact (K : Set (Matrix (Fin d) (Fin a) F.Carrier)) →
          0 < rectangularMeasure η d a K ∧ rectangularMeasure η d a K < ∞ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  intro η K hK
  exact ⟨K.isOpen.measure_pos _ ⟨0, K.zero_mem⟩, hK.measure_lt_top⟩

section Transfer

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A positive finite scalar times a measurable pushforward gives absolute
integrability in both directions and the exact complex integral formula. -/
theorem complex_integral_transfer_of_positive_scaled_map
    (ν : Measure X) (μ : Measure Y) (chart : X → Y) (hchart : Measurable chart)
    (C : ℝ) (hC : 0 < C)
    (hμ : μ = ENNReal.ofReal C • Measure.map chart ν)
    (f : Y → ℂ) (hf : Measurable f) :
    (Integrable f μ ↔ Integrable (f ∘ chart) ν) ∧
      (∫ q, f q ∂μ) = (C : ℂ) * ∫ z, f (chart z) ∂ν := by
  constructor
  · rw [hμ, integrable_smul_measure (ENNReal.ofReal_pos.mpr hC).ne'
      ENNReal.ofReal_ne_top]
    exact integrable_map_measure hf.aestronglyMeasurable hchart.aemeasurable
  · rw [hμ, integral_smul_measure, integral_map hchart.aemeasurable hf.aestronglyMeasurable,
      ENNReal.toReal_ofReal hC.le, Complex.real_smul]

end Transfer

end Langlands.RankinSelberg
