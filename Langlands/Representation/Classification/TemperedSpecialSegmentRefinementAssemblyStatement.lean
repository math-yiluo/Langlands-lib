import Langlands.Representation.Classification.TemperedSpecialSegmentRefinementStatement
import Langlands.Representation.Classification.TemperedBlockStatement
import Langlands.Representation.Classification.SegmentSquareIntegrabilityStatement
import Langlands.Representation.Classification.LinkedSegmentHeadExponentStatement
import Langlands.Representation.Parabolic.OrderedProductRegroupingStatement

/-! An internal conditional assembly interface for special-segment refinement. -/

namespace Langlands.Classification

universe uF uV

variable {p : Nat} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The four named inputs suffice to refine tempered Langlands data into ordered
strong special-segment heads with an isomorphic normalized product. -/
def TemperedSpecialSegmentRefinementAssembly : Prop :=
  TemperedBlockExhaustion.{uF,uV} F T →
  SegmentEssentialSquareIntegrableClassification.{uF,uV} F T →
  LinkedSegmentHeadExponentComparison.{uF,uV} F T →
  Parabolic.OrderedProductRegrouping.{uF,max uF uV} F T →
  TemperedSpecialSegmentRefinement.{uF,uV} F T

end Langlands.Classification
