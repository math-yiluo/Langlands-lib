import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLDensity
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof
/-! The determinant density relating matrix additive Haar and actual GL Haar. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology
open scoped NNReal ENNReal

namespace Langlands.AllField.RankinSelberg.GLDeterminantDensity
open Langlands.RankinSelberg.GLDeterminantDensity hiding padic_exists_weightedRestriction_eq_generalLinearHaar padic_weightedRestriction_isHaar
open Langlands.AllField.RankinSelberg.GLDeterminantDensity
open Langlands.RankinSelberg hiding LastRowCompactOrbitStatement lastRowCompactOrbit
open Langlands.AllField.RankinSelberg

universe uK

section Measure


end Measure

section Algebra



end Algebra

section Topology


end Topology

section General



end General

section Integrals


end Integrals

universe uF

/-- The genuine residue-normalized determinant density gives Haar measure for
every supplied p-adic realization and every additive matrix Haar measure. -/
theorem padic_weightedRestriction_isHaar 
    (F : Type uF) [Field F] (T : LocalFieldData F) (r : ℕ) :
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin r) (Fin r) F)]
      [BorelSpace (Matrix (Fin r) (Fin r) F)]
      [MeasurableSpace (GeneralLinear r F)] [BorelSpace (GeneralLinear r F)]
      (μ : Measure (Matrix (Fin r) (Fin r) F)) [IsAddHaarMeasure μ],
      IsHaarMeasure (weightedRestriction r T.normalizedAbsHom μ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let : LocallyCompactSpace (GeneralLinear r F) := T.generalLinearLocallyCompactSpace r
  intro _ _ _ _ μ _
  apply weightedRestriction_isHaar r T.normalizedAbsHom T.continuous_normalizedAbsHom μ
  intro g
  have h := Langlands.AllField.HarmonicAnalysis.padicRectangularHaarScaling F T r r μ g 1
  simp only [inv_one, Units.val_one, Matrix.mul_one, map_one, one_pow, div_one] at h
  rw [weight_eq, inv_pow]
  exact h

/-- Comparison with the canonical actual GL Haar measure, normalized on integral
matrices. The scalar is positive and depends on the supplied additive measure. -/
theorem padic_exists_weightedRestriction_eq_generalLinearHaar 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) F)]
      [BorelSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) F)]
      [MeasurableSpace (GeneralLinear (n + 1) F)]
      [BorelSpace (GeneralLinear (n + 1) F)]
      (μ : Measure (Matrix (Fin (n + 1)) (Fin (n + 1)) F)) [IsAddHaarMeasure μ],
      ∃ c : ℝ≥0, 0 < c ∧ weightedRestriction (n + 1) T.normalizedAbsHom μ =
        c • generalLinearHaar F n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : LocallyCompactSpace (GeneralLinear (n + 1) F) :=
    T.generalLinearLocallyCompactSpace (n + 1)
  let := T.secondCountableTopology
  let : SecondCountableTopology (Matrix (Fin (n + 1)) (Fin (n + 1)) F) :=
    inferInstanceAs (SecondCountableTopology (Fin (n + 1) → Fin (n + 1) → F))
  let : SecondCountableTopology (GeneralLinear (n + 1) F) :=
    (isEmbedding_generalLinear_val (K := F) (n + 1)).secondCountableTopology
  intro _ _ _ _ μ _
  let : IsHaarMeasure (weightedRestriction (n + 1) T.normalizedAbsHom μ) :=
    padic_weightedRestriction_isHaar F T (n + 1) μ
  exact ⟨haarScalarFactor (weightedRestriction (n + 1) T.normalizedAbsHom μ)
      (generalLinearHaar F n), haarScalarFactor_pos_of_isHaarMeasure _ _,
      isMulLeftInvariant_eq_smul _ _⟩

end Langlands.AllField.RankinSelberg.GLDeterminantDensity
