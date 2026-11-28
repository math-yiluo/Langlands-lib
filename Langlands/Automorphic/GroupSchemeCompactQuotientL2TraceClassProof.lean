import Langlands.Automorphic.GroupSchemeCompactQuotientL2TraceClassStatement
import Langlands.Analysis.Local.CompactQuotientConvolutionTraceClassProof
import Langlands.Global.AdelicSplitCenterWeil

/-! # Trace-class convolution products on the compact positive rational quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.QuotientIntegration

set_option maxHeartbeats 2000000 in
/-- The convolution product of two compactly supported continuous adelic
weights acts by a trace-class operator on the compact quotient. -/
theorem groupSchemeCompactQuotientL2TraceClass :
    GroupSchemeCompactQuotientL2TraceClassStatement.{u} := by
  intro F _ _ G _ _ T i hi _ I _ e hc _ hcompact
  dsimp only
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isHaarMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_sigmaFinite F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isMulRightInvariant F G T i hi I e hc
  refine compactQuotientConvolutionTraceClass
    (positiveRationalSubgroup F G T i) (isClosed_positiveRationalSubgroup F G T i hi I e hc)
    (positiveRationalSubgroupHaarMeasure F G T i hi I e hc)
    Measure.haar (positiveRationalQuotientHaarMeasure F G T i)
    (positiveRationalQuotientHaarMeasure_isCompatible F G T i hi I e hc) hcompact
    (haarQuotientL2BoundedRightAction F G T i hi I e hc)
    (norm_haarQuotientL2BoundedRightAction F G T i hi I e hc)
    (haarQuotientL2Orbit_aestronglyMeasurable F G T i hi I e hc Measure.haar) ?_
  intro a φ
  refine (coeFn_quotientL2RightTranslate F G T i _
    (haarQuotientMeasureRightInvariant F G T i hi I e hc) a φ).trans ?_
  exact Filter.Eventually.of_forall fun q => by
    induction q using Quotient.inductionOn with
    | _ x => rfl

end Langlands.Automorphic.GroupSchemeFunctions
