import Langlands.HarmonicAnalysis.PadicHaarScalingStatement
import Langlands.AllField.Group.GL.NormalizedCharacter
/-!
# Residue-normalized additive Haar change of variables

Internal prerequisite statements for the block-unipotent modulus computation.
These definitions state scalar and rectangular change-of-variables identities;
they do not prove them.
-/

open scoped NNReal

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement
open Langlands.AllField.HarmonicAnalysis

universe uF

/-- Left and inverse-right multiplication on rectangular matrices has the
expected determinant factor, for every additive Haar measure. -/
def PadicRectangularHaarScalingStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F)
    (r s : ℕ),
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin r) (Fin s) F)]
      [BorelSpace (Matrix (Fin r) (Fin s) F)]
      (μ : MeasureTheory.Measure (Matrix (Fin r) (Fin s) F))
      [MeasureTheory.Measure.IsAddHaarMeasure μ]
      (A : GeneralLinear r F) (B : GeneralLinear s F),
      μ.map (fun X => (A : Matrix (Fin r) (Fin r) F) * X *
        ((B⁻¹ : GeneralLinear s F) : Matrix (Fin s) (Fin s) F)) =
        (((T.determinantNorm r A : ℝ≥0) ^ s /
          (T.determinantNorm s B : ℝ≥0) ^ r)⁻¹) • μ

end Langlands.AllField.HarmonicAnalysis
