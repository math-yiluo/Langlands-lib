import Langlands.AllFieldBZ.Representation.Parabolic.OrderedRefinementTensorInduction
import Langlands.Representation.Parabolic.RefinedInnerInductionObjects

/-!
# All-field port of `Langlands.Representation.Parabolic.RefinedInnerInductionObjects`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.RefinedInnerInductionObjects` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding MinimalNonzeroJacquetTheorem minimalNonzeroJacquet refinedInnerInductionObjects
open Langlands.GeneralLinear
open Langlands.Parabolic hiding NormalizedRefinementInductionTransitivityClause ParabolicQuotientCompactClause RefinedInductionTensorTheorem RefinementCoordinatesNormalizationTheorem UnipotentFiniteContainmentClause isCompact_integralRange normalizedRefinementInductionTransitivity orderedRefinementInductionEquiv orderedRefinementIteratedInduced orderedRefinementTensorFactors orderedRefinementTensorInductionEquiv parabolicQuotientCompact quotientMap_image_integralRange refinedInductionTensor refinementCoordinatesNormalization
open Langlands.AllFieldBZ.Parabolic
universe uF uV

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

/-- The actual smooth objects for normalized induction inside each refined
block of a common outer Levi. -/
def refinedInnerInductionObjects {r : ℕ} (D : BlockShape r)
    (S : Langlands.Geometric.BlockRefinement D)
    (C : Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.Factors.{uF,uV} F T D S) :
    letI := T.topology
    ∀ m, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (D.size m) F.Carrier) :=
  letI := T.topology
  fun m => SmoothRep.of (Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.blockRepresentations F T D S C m)
    (T.isSmooth_normalizedParabolicInduced (S m) (C m).representation)

end Langlands.AllFieldBZ.CuspidalSupport
