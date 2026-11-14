import Langlands.Representation.Shahidi.JacquetDiagonalProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetData
import Langlands.AllField.Representation.Shahidi.JacquetDiagonalStatement
/-! # Scalar Jacquet covariance under exchanged unipotent diagonal blocks -/

noncomputable section

namespace Langlands.AllField.Shahidi
open Langlands.Shahidi hiding JacquetDiagonalCovarianceStatement jacquetDiagonalCovariance map_rectangularConj_padic
open Langlands.AllField.Shahidi

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV

section Algebra




end Algebra

section Integral


end Integral

/-- The closed scalar unipotent diagonal prerequisite for the JPSS construction. -/
theorem jacquetDiagonalCovariance : JacquetDiagonalCovarianceStatement.{uF, uV} := by
  intro F _ T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.fieldT2
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro V _ _ ψ m n ℓ μ _ u₁ u₂ z f hf
  have hnorm (r : ℕ) (u : upperUnipotent r F) :
      T.determinantNorm r u.val = 1 := by
    have hd : GeneralLinear.determinant u.val = 1 :=
      Units.ext (RankinSelberg.unipotent_det u)
    change T.normalizedAbsUnits (GeneralLinear.determinant u.val) = 1
    rw [hd, map_one]
  have hμ : μ.map (rectangularConj u₂.val u₁.val) = μ := by
    simpa only [hnorm, Units.val_one, one_pow, div_one, one_smul] using
      (map_rectangularConj_padic F T μ u₂.val u₁.val)
  refine ⟨hμ, ?_, ?_⟩
  · intro x
    exact jacquetIntegrand_rightTranslate_unipotent_blockSum ψ ℓ u₁ u₂ z f hf x
  · intro hi
    exact ⟨integrable_jacquetIntegrand_rightTranslate_unipotent_blockSum
        ψ ℓ μ u₁ u₂ z f hf hμ hi,
      integral_jacquetIntegrand_rightTranslate_unipotent_blockSum ψ ℓ μ u₁ u₂ z f hf hμ⟩

end Langlands.AllField.Shahidi
