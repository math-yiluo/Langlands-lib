import Langlands.BruhatTits.IntegralModels.UnramifiedFacetCommonTorusStatement
import Langlands.BruhatTits.IntegralModels.CommonTorusQuotientMaximality
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetSignDescent
import Langlands.BruhatTits.IntegralModels.UnramifiedFacetLieWeightSignAssembly
import Langlands.Geometry.Building.UnramifiedDescendedApartmentTorusProof

/-! # Common maximal split tori and Lie-weight signs for descended facet models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.BruhatTits.IntegralModels

open Langlands.GroupScheme Langlands.Geometry.Building

/-- Common maximal split tori and the Lie-weight sign formula for incident
facets of the descended building, with the supplied integral torus. -/
theorem unramifiedFacetCommonTorus : UnramifiedFacetCommonTorusStatement.{u} := by
  intro F _ _ _ _ G _ P R T h₁ h₂ h₃ h₄ h₅ h₆ h₇ C A e a
    he_inj he ha hgal hfixed hspecial hfacet hbounded E Fc Fc' g Fa Fa'
    hface hFc hFc' D D' _ _ hD hD' φ Q torus hQ hT
  have hmax := φ.hasMaximalSplitTori_integer P g Q torus hQ hT
  refine ⟨hmax.2.1, hmax.2.2, ?_⟩
  intro hSplit
  exact unramifiedFacetLieWeightSignFormula_of_descent
    unramifiedFacetLieWeightSign unramifiedDescendedApartmentTorus
    F G P R T h₁ h₂ h₃ h₄ h₅ h₆ h₇ C A e a
    he_inj he ha hgal hfixed hspecial hfacet hbounded E Fc Fc' g Fa Fa'
    hface hFc hFc' D D' hD hD' φ Q torus hQ hSplit

end Langlands.BruhatTits.IntegralModels
