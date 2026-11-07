import Langlands.Representation.Classification.TemperedSpecialSegmentRefinementAssembly
import Langlands.Representation.Classification.TemperedBlockExhaustionProof
import Langlands.Representation.Classification.SegmentEssentialSquareIntegrableClassificationProof
import Langlands.Representation.Classification.LinkedSegmentHeadExponentProof
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof

/-!
# Tempered Langlands data refined into ordered special segments

Discharge the four premises of the published refinement assembly with their
closed proofs, retaining the exact unconditional refinement statement.
-/

namespace Langlands.Classification

universe uF uV

/-- Every positive-rank tempered Langlands datum has an ordered strong
special-segment datum with an isomorphic actual normalized induced object. -/
theorem temperedSpecialSegmentRefinement
    {p : Nat} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TemperedSpecialSegmentRefinement.{uF,uV} F T :=
  temperedSpecialSegmentRefinementAssembly.{uF,uV} F T
    (temperedBlockExhaustion.{uF,uV} F T)
    (segmentEssentialSquareIntegrableClassification.{uF,uV} F T)
    (linkedSegmentHeadExponentComparison.{uF,uV} F T)
    (Parabolic.orderedProductRegrouping.{uF,max uF uV} F T)

end Langlands.Classification
