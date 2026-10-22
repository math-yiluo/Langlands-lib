import Langlands.Group.GL.NormalizedCharacter
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Residue-normalized additive Haar change of variables

Internal prerequisite statements for the block-unipotent modulus computation.
These definitions state scalar and rectangular change-of-variables identities;
they do not prove them.
-/

open scoped NNReal

namespace Langlands.HarmonicAnalysis

universe uF

/-- Multiplication by a field unit pushes every additive Haar measure forward by
its inverse residue-normalized absolute value. -/
def PadicScalarHaarScalingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ [MeasurableSpace F.Carrier] [BorelSpace F.Carrier]
      (μ : MeasureTheory.Measure F.Carrier)
      [MeasureTheory.Measure.IsAddHaarMeasure μ] (a : F.Carrierˣ),
      μ.map (fun x => (a : F.Carrier) * x) =
        ((T.normalizedAbsUnits a : ℝ≥0)⁻¹) • μ

/-- Left and inverse-right multiplication on rectangular matrices has the
expected determinant factor, for every additive Haar measure. -/
def PadicRectangularHaarScalingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (r s : ℕ),
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin r) (Fin s) F.Carrier)]
      [BorelSpace (Matrix (Fin r) (Fin s) F.Carrier)]
      (μ : MeasureTheory.Measure (Matrix (Fin r) (Fin s) F.Carrier))
      [MeasureTheory.Measure.IsAddHaarMeasure μ]
      (A : GeneralLinear r F.Carrier) (B : GeneralLinear s F.Carrier),
      μ.map (fun X => (A : Matrix (Fin r) (Fin r) F.Carrier) * X *
        ((B⁻¹ : GeneralLinear s F.Carrier) : Matrix (Fin s) (Fin s) F.Carrier)) =
        (((T.determinantNorm r A : ℝ≥0) ^ s /
          (T.determinantNorm s B : ℝ≥0) ^ r)⁻¹) • μ

/-- The two additive change-of-variables prerequisites for the block modulus. -/
def PadicAdditiveHaarScalingStatement : Prop :=
  PadicScalarHaarScalingStatement.{uF} ∧ PadicRectangularHaarScalingStatement.{uF}

end Langlands.HarmonicAnalysis
