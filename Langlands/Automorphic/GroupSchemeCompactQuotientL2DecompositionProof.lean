import Langlands.Automorphic.GroupSchemeCompactQuotientL2DecompositionStatement
import Langlands.Analysis.Local.CompactQuotientDiscreteDecompositionProof
import Langlands.Global.AdelicSplitCenterWeil

/-! # Discrete decomposition of the compact positive rational quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.QuotientIntegration

set_option maxHeartbeats 2000000 in
/-- A compact positive rational quotient has Hilbert–Schmidt convolutions
and a discrete Hilbert decomposition with finite multiplicities. -/
theorem groupSchemeCompactQuotientL2Decomposition :
    GroupSchemeCompactQuotientL2DecompositionStatement.{u} := by
  intro F _ _ G _ _ T i hi _ I _ e hc _ hcompact
  dsimp only
  let H := positiveRationalSubgroup F G T i
  let μH := positiveRationalSubgroupHaarMeasure F G T i hi I e hc
  let μG : Measure (AdelicGroupPoints F G) := Measure.haar
  let μQ := positiveRationalQuotientHaarMeasure F G T i
  let π := haarQuotientL2BoundedRightAction F G T i hi I e hc
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isHaarMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_sigmaFinite F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isMulRightInvariant F G T i hi I e hc
  have hH := isClosed_positiveRationalSubgroup F G T i hi I e hc
  have hQ := positiveRationalQuotientHaarMeasure_isCompatible F G T i hi I e hc
  have hπapply (a : AdelicGroupPoints F G) (φ : Lp ℂ 2 μQ) :
      (π a φ : LeftQuotient H → ℂ) =ᵐ[μQ] fun q => φ (rightTranslate H a q) := by
    refine (coeFn_quotientL2RightTranslate F G T i _
      (haarQuotientMeasureRightInvariant F G T i hi I e hc) a φ).trans ?_
    exact Filter.Eventually.of_forall fun q => by
      induction q using Quotient.inductionOn with
      | _ x => rfl
  refine ⟨compactQuotientIntegratedHilbertSchmidt H hH μH μG μQ hQ hcompact π
    (norm_haarQuotientL2BoundedRightAction F G T i hi I e hc)
    (haarQuotientL2Orbit_aestronglyMeasurable F G T i hi I e hc μG) hπapply, ?_⟩
  exact compactQuotientDiscreteDecomposition H hH μH μG μQ hQ hcompact π
    (fun a φ ψ => (quotientL2RightTranslate F G T i μQ
      (haarQuotientMeasureRightInvariant F G T i hi I e hc) a).inner_map_map φ ψ)
    (fun φ => (haarQuotientL2OrbitMap F G T i hi I e hc φ).continuous) hπapply

end Langlands.Automorphic.GroupSchemeFunctions
