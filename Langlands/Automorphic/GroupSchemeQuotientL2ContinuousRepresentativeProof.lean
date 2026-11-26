import Langlands.Automorphic.GroupSchemeQuotientL2ContinuousRepresentativeStatement
import Langlands.Analysis.Local.QuotientIntegratedContinuousRepresentativeProof
import Langlands.Global.AdelicSplitCenterWeil

/-! # Continuous representatives on the positive rational quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported Pointwise

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.QuotientIntegration

/-- Compactly supported continuous weights give continuous representatives on the
positive rational quotient, with the pointwise subgroup-measure bound. -/
theorem groupSchemeQuotientL2ContinuousRepresentative :
    GroupSchemeQuotientL2ContinuousRepresentativeStatement.{u} := by
  intro F _ _ G _ _ T i hi _ I _ e hc _
  dsimp only
  intro f hf φ
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isHaarMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_sigmaFinite F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isMulRightInvariant F G T i hi I e hc
  refine quotientIntegratedContinuousRepresentative
    (positiveRationalSubgroup F G T i) (isClosed_positiveRationalSubgroup F G T i hi I e hc)
    (positiveRationalSubgroupHaarMeasure F G T i hi I e hc)
    Measure.haar (positiveRationalQuotientHaarMeasure F G T i)
    (positiveRationalQuotientHaarMeasure_isCompatible F G T i hi I e hc)
    (haarQuotientL2BoundedRightAction F G T i hi I e hc)
    (norm_haarQuotientL2BoundedRightAction F G T i hi I e hc)
    (haarQuotientL2Orbit_aestronglyMeasurable F G T i hi I e hc Measure.haar) ?_ f hf φ
  intro g v
  refine (coeFn_quotientL2RightTranslate F G T i _
    (haarQuotientMeasureRightInvariant F G T i hi I e hc) g v).trans ?_
  exact Filter.Eventually.of_forall fun q => by
    induction q using Quotient.inductionOn with
    | _ x => rfl

end Langlands.Automorphic.GroupSchemeFunctions
