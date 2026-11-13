import Langlands.Representation.RankinSelberg.UnequalRankFourierSmearingProof
import Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankFourierSmearingStatement
/-! Global and pointwise JPSS Fourier smearing with one same-model coefficient. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankFourierSmearingStatement unequalRankFourierSmearingStatement
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker

universe uF uV

/-- The exact supplied-pair Fourier-smearing proposition, in independent universes. -/
theorem unequalRankFourierSmearingStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n j k : ℕ) :
    UnequalRankFourierSmearingStatement.{uF,uV} F T n j k := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  intro ψ ν V _ _ π hπ ℓ f κ Φ hpair
  obtain ⟨f₁, hglobal⟩ := Smearing.exists_coefficient_average (rowMeasure ν (n + 1))
    π hπ ℓ (unequalRankSmearingUnipotent n j k)
    (continuous_unequalRankSmearingUnipotent n j k) κ f
  refine ⟨f₁, hglobal, ?_⟩
  intro g X
  rw [(hglobal (unequalRankMatrix (j + 1) k g X)).2]
  calc
    (∫ z, κ z * f.val.val
        (unequalRankMatrix (j + 1) k g X * unequalRankSmearingUnipotent n j k z)
        ∂rowMeasure ν (n + 1)) =
      ∫ z, (ψ.complex (rowPairing z (X (Fin.last j))) * κ z) *
        f.val.val (unequalRankMatrix (j + 1) k g X) ∂rowMeasure ν (n + 1) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [unequalRankMatrix_smearing_coefficient ψ π ℓ f]
      ring
    _ = rowFourierIntegral ψ ν (n + 1) κ (X (Fin.last j)) *
        f.val.val (unequalRankMatrix (j + 1) k g X) := integral_mul_const _ _
    _ = Φ (X (Fin.last j)) * f.val.val (unequalRankMatrix (j + 1) k g X) := by
      rw [← hpair (X (Fin.last j))]

end Langlands.AllField.RankinSelberg
