import Langlands.Representation.RankinSelberg.EqualRankLastRowReductionProof
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankLastRowReductionStatement
import Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof
/-!
# Equal-rank integrals with a last-row orbit cutoff: proof
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankLastRowReductionStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement equalRankLastRowReduction lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

namespace LastRowReduction
open Langlands.RankinSelberg.LastRowReduction
open Langlands.AllField.RankinSelberg.LastRowReduction
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankLastRowReductionStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement equalRankLastRowReduction lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.QuotientIntegration

section Algebra


end Algebra

section PiecewiseConstant

open scoped NNReal ENNReal


end PiecewiseConstant

section CompactDeterminant

open scoped NNReal

end CompactDeterminant

section Level


end Level

section Coordinates


end Coordinates

section HaarFiber

open scoped NNReal ENNReal
open Measure


end HaarFiber

section Orbits


end Orbits

section OrbitMass

open scoped ENNReal



end OrbitMass

section LocallyConstant

end LocallyConstant

section Compare

end Compare

section Invariance

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open scoped NNReal



end Invariance

section OrbitIndex


end OrbitIndex

section Main

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open scoped NNReal ENNReal


end Main

end LastRowReduction

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.LastRowReduction
open Langlands.AllField.RankinSelberg.LastRowReduction

universe uF

set_option linter.overlappingInstances false in
/-- The last-row reduction over a `p`-adic field: specialize the general theorem to
`χ = |·|_F`, additive Haar measure on the last column, and the normalized Haar measures. -/
theorem equalRankLastRowReduction (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) : EqualRankLastRowReductionStatement F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F := T.fieldT2
  have : SecondCountableTopology F := T.secondCountableTopology
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  have := T.generalLinearT2Space (n + 1)
  have := T.generalLinearLocallyCompactSpace (n + 1)
  have := T.generalLinearSecondCountableTopology (n + 1)
  have := T.generalLinearT2Space (n + 1 + 1)
  have := T.generalLinearLocallyCompactSpace (n + 1 + 1)
  have := T.generalLinearSecondCountableTopology (n + 1 + 1)
  let := borel (Langlands.GeneralLinear (n + 1) F)
  have : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  have : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  have : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1 + 1) F)
  have : BorelSpace (Langlands.GeneralLinear (n + 1 + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1 + 1) F)
  have : BorelSpace (upperUnipotent (n + 1 + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (n + 1) F)
  have : BorelSpace (LeftUnipotentQuotient (n + 1) F) := ⟨rfl⟩
  intro _ _ μ μ' hμ hμ' J hJ
  have hχ (a : F) (ha : a ≠ 0) :
      (Measure.addHaar : Measure F).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • Measure.addHaar :=
    Langlands.AllField.HarmonicAnalysis.padicScalarHaarScaling F T Measure.addHaar (Units.mk0 a ha)
  have hdet : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) F, M.det ≠ 0 →
      (Measure.addHaar : Measure (Fin (n + 1) → F)).map (Matrix.toLin' M) =
        (T.normalizedAbsHom M.det)⁻¹ • Measure.addHaar :=
    fun M hM => HarmonicAnalysis.haarMeasure_map_matrix (Measure.addHaar : Measure F)
      T.normalizedAbsHom hχ _ hM
  have hJ1 : ∀ j ∈ J, T.normalizedAbsHom (Matrix.det j.val) = 1 := by
    intro j hj
    have h := eq_one_of_isCompact (T.determinantNorm (n + 1 + 1))
      (T.determinantNormContinuous (n + 1 + 1)).continuous J.toSubgroup hJ hj
    exact congrArg Units.val h
  exact lastRowReduction T.normalizedAbsHom (normalizedAbsoluteValue T) (fun _ => rfl)
    Measure.addHaar hdet (generalLinearHaar F (n + 1)) (unipotentHaar F (n + 1))
    (generalLinearHaar F n) (unipotentHaar F n) μ μ' hμ hμ' J hJ hJ1

end Langlands.AllField.RankinSelberg
