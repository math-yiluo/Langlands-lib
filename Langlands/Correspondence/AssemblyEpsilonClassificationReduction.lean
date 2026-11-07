import Langlands.Correspondence.BlockPairGammaReduction
import Langlands.Correspondence.AssemblyDatumMatching
import Langlands.Correspondence.AssemblyLDatumExistence
import Langlands.LocalFactor.WeilDeligneEulerPairBlockProof
import Langlands.Representation.RankinSelberg.SegmentHeadGammaFactorProof

/-!
# Epsilon inheritance from classification and the segment-head L formula

All premises of the conditional epsilon-inheritance reductions that are now
proved in the Library are discharged here: the pair-block Euler formula
(`LocalFactor.wdEulerPairBlock`), hence the block-pair gamma law; the
segment-head gamma formula (`RankinSelberg.segmentHeadGammaFactor`); and the
existence of segment-head presenting data (`multisegmentHeadDatumExistence`).
Two premises remain explicit: the square-integrable Langlands classification
and the segment-head L-factor formula.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The block-pair gamma law (Henniart 2002, §2.4), unconditionally. -/
theorem blockPairGamma : LocalFactor.PairBlock.BlockPairGamma.{uF, uP} F :=
  LocalFactor.CommonClosureGamma.blockPairGamma_of_wdEulerPairBlock F
    LocalFactor.wdEulerPairBlock

/-- Epsilon inheritance for the assembled correspondence follows from the
square-integrable Langlands classification and the segment-head L-factor
formula. -/
def AssemblyEpsilonClassificationReductionStatement : Prop :=
  Classification.SquareIntegrableLanglandsClassification.{uF, uA}
      F F.canonicalTopologicalData →
    RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA} →
      AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F

/-- Epsilon inheritance from the square-integrable classification and the
segment-head L-factor formula. -/
theorem assemblyEpsilonInheritance_of_classification_of_segmentHeadL
    (hC : Classification.SquareIntegrableLanglandsClassification.{uF, uA}
      F F.canonicalTopologicalData)
    (hL : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA}) :
    AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F :=
  assemblyEpsilonInheritance_of_segmentHeads F
    (multisegmentHeadDatumMatching_of_existence_and_classification F
      (multisegmentHeadDatumExistence F) hC)
    hL RankinSelberg.segmentHeadGammaFactor (blockPairGamma F) LocalFactor.wdEulerPairBlock

theorem assemblyEpsilonClassificationReduction :
    AssemblyEpsilonClassificationReductionStatement.{uF, uP, uA} F :=
  assemblyEpsilonInheritance_of_classification_of_segmentHeadL F

end Langlands.Correspondence
