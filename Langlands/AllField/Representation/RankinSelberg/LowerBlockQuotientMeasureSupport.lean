import Langlands.Representation.RankinSelberg.LowerBlockQuotientMeasureSupport
import Langlands.AllField.Group.GL.PadicBlocksSupplement
import Langlands.AllField.Representation.RankinSelberg.LowerBlockQuotientDisintegrationStatement
/-!
# Measure support for lower-block quotient disintegration

Right Haar measure on the actual lower triangular group, positive finite
compact open volumes, and integral transfer from a positive scaled pushforward.
These results do not assert the lower-block measure identity.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Langlands.AllField.GeneralLinear
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe u

end Langlands.AllField.GeneralLinear

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding LowerBlockQuotientDisintegrationStatement continuous_lowerBlockQuotientDensity lowerBlockDensity_unipotent_mul lowerBlockQuotientDensity lowerBlockQuotientDensity_mk lowerTriangularRightHaar lowerTriangularRightHaar_properties measurable_lowerBlockQuotientDensity rectangularMeasure_compactOpen_pos_lt_top
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe uF

section RightHaar

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- Inversion sends a left Haar measure to a right Haar measure on the actual
lower triangular group, with no normalization imposed. -/
def lowerTriangularRightHaar (d : ℕ) :
    letI := T.topology
    letI := borel (lowerTriangularSubgroup d F)
    Measure (lowerTriangularSubgroup d F) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace d
  let : LocallyCompactSpace (lowerTriangularSubgroup d F) :=
    (lowerTriangularSubgroup_isClosed d).locallyCompactSpace
  let := borel (lowerTriangularSubgroup d F)
  have : BorelSpace (lowerTriangularSubgroup d F) := ⟨rfl⟩
  exact (Measure.haar : Measure (lowerTriangularSubgroup d F)).inv

/-- All regularity, finiteness and right-invariance properties required of the
triangular measure in lower-block disintegration. -/
theorem lowerTriangularRightHaar_properties (d : ℕ) :
    letI := T.topology
    letI := borel (lowerTriangularSubgroup d F)
    let ρ := lowerTriangularRightHaar F T d
    ρ.Regular ∧ SigmaFinite ρ ∧ ρ.IsOpenPosMeasure ∧ IsFiniteMeasureOnCompacts ρ ∧
      ρ.IsMulRightInvariant ∧
      (∀ K : OpenSubgroup (lowerTriangularSubgroup d F),
        IsCompact (K : Set (lowerTriangularSubgroup d F)) →
          0 < ρ K ∧ ρ K < ∞) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace d
  let := T.generalLinearSecondCountableTopology d
  let : SecondCountableTopology (lowerTriangularSubgroup d F) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : LocallyCompactSpace (lowerTriangularSubgroup d F) :=
    (lowerTriangularSubgroup_isClosed d).locallyCompactSpace
  let := borel (lowerTriangularSubgroup d F)
  have : BorelSpace (lowerTriangularSubgroup d F) := ⟨rfl⟩
  dsimp only [lowerTriangularRightHaar]
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro K hK
  exact ⟨K.isOpen.measure_pos _ ⟨1, K.one_mem⟩, hK.measure_lt_top⟩

end RightHaar

/-- Every compact open additive parameter subgroup has positive finite volume
for every supplied scalar Haar measure. -/
theorem rectangularMeasure_compactOpen_pos_lt_top 
    (F : Type uF) [Field F] (T : LocalFieldData F) (d a : ℕ) :
    letI := T.topology
    letI := borel F
    ∀ η : AdditiveHaarMeasure F,
      ∀ K : OpenAddSubgroup (Matrix (Fin d) (Fin a) F),
        IsCompact (K : Set (Matrix (Fin d) (Fin a) F)) →
          0 < rectangularMeasure η d a K ∧ rectangularMeasure η d a K < ∞ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  intro η K hK
  exact ⟨K.isOpen.measure_pos _ ⟨0, K.zero_mem⟩, hK.measure_lt_top⟩

section Transfer


end Transfer

end Langlands.AllField.RankinSelberg
