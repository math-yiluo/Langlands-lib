import Langlands.Representation.Classification.SegmentSocleProductHomogeneityAssembly
import Langlands.Representation.Derivative.LeftMixedProductDerivativeProof
import Langlands.Representation.Derivative.LeftMixedProductHomogeneityProof
import Langlands.Representation.Derivative.MirabolicMinusExactnessProof
import Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary
import Langlands.Representation.Derivative.MirabolicProductMinusRightPhi
import Langlands.Representation.Derivative.RightMixedProductPhiMinusDetectionProof
import Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftProof
import Langlands.Representation.Classification.SegmentSocleDerivativesProof
import Langlands.Representation.Classification.SegmentSocleProductHighestDerivativeProof

/-!
# Zelevinsky 6.2: homogeneity of endpoint-separated segment-socle products

The published assembly `segmentSocleProductHomogeneity_of` derives
`SegmentSocleProductHomogeneity` from nine published input statements. Each of
those inputs now has a published proof, and this module supplies them.
-/

noncomputable section

namespace Langlands.Classification

open Derivative

universe uF uV

/-- Zelevinsky, *Induced representations II*, Theorem 6.2: every actual ordered
product of segment socles whose earlier segments never end just before a later
segment begins is homogeneous. -/
theorem segmentSocleProductHomogeneity {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentSocleProductHomogeneity.{uF, uV} F T :=
  segmentSocleProductHomogeneity_of T
    (Mirabolic.minusExactness.{uF, max uF uV} F T)
    (MirabolicProductMinus.rightPhiShortExact.{uF, max uF uV} (F := F) T)
    (MirabolicProductMinus.rightPhiBoundary.{uF, max uF uV} (F := F) T)
    (rightMixedProductPhiMinusDetection.{uF, max uF uV} F T)
    (leftMixedProductDerivative.{uF, max uF uV} F T)
    (leftMixedProductHomogeneity.{uF, max uF uV} F T)
    (segmentSocleDerivatives.{uF, uV} F T)
    (segmentSocleProductHighestDerivative.{uF, uV} F T)
    (cuspidalProductMirabolicSupportShift.{uF, uV} F T)

end Langlands.Classification
