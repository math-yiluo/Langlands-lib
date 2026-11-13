import Langlands.BruhatTits.MaximalProP.AvailableStatement
import Langlands.BruhatTits.IntegralModels.DepthZeroCompactOpen
import Langlands.AlgebraicGeometry.PointTopology.RationalPointEvaluation

/-! # Topology and basic inclusions of available facet radical preimages -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels
  Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.MaximalProP

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local instance genericAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance genericPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance genericPointTotallyDisconnected : TotallyDisconnectedSpace (rationalPoints G) :=
  rationalPoint_totallyDisconnectedSpace_of_localField F G.X

variable (D : KPBuildingDatum G) (Fa : BuildingFacet D.base.toValuationBuildingData)

/-- The radical preimage of every supplied facet model is open in the point topology. -/
theorem isOpen_facetPositiveSubgroup [LocallyOfFiniteType G.X.hom] :
    IsOpen (facetPositiveSubgroup D Fa : Set (rationalPoints G)) :=
  (D.quotients.quotient Fa).localField_isOpen_positivePoints

/-- The same radical preimage is compact. -/
theorem isCompact_facetPositiveSubgroup [LocallyOfFiniteType G.X.hom] :
    IsCompact (facetPositiveSubgroup D Fa : Set (rationalPoints G)) :=
  (D.quotients.quotient Fa).localField_isCompact_positivePoints

/-- Bundle the existing radical preimage as an open subgroup in the point topology. -/
def facetPositiveOpenSubgroup [LocallyOfFiniteType G.X.hom] :
    OpenSubgroup (rationalPoints G) :=
  ⟨facetPositiveSubgroup D Fa, isOpen_facetPositiveSubgroup D Fa⟩

@[simp] theorem facetPositiveOpenSubgroup_toSubgroup [LocallyOfFiniteType G.X.hom] :
    (facetPositiveOpenSubgroup D Fa).toSubgroup = facetPositiveSubgroup D Fa := rfl

/-- The subgroup has a compact subspace topology. -/
theorem compactSpace_facetPositiveSubgroup [LocallyOfFiniteType G.X.hom] :
    CompactSpace (facetPositiveSubgroup D Fa) :=
  isCompact_iff_compactSpace.mp (isCompact_facetPositiveSubgroup D Fa)

/-- The point topology restricts to a totally disconnected topology on the radical preimage. -/
theorem totallyDisconnectedSpace_facetPositiveSubgroup :
    TotallyDisconnectedSpace (facetPositiveSubgroup D Fa) := inferInstance

/-- Axiom 4.1.20 places the radical preimage in the facet's zero fixer. -/
theorem facetPositiveSubgroup_le_facetZeroFixer (hD : D.SatisfiesGroupAxioms) :
    facetPositiveSubgroup D Fa ≤ facetZeroFixer D Fa := by
  change (D.quotients.quotient Fa).positivePoints ≤
    BuildingModelFamily.zeroFixer D.base (BuildingModelIndex.ofFacet Fa)
  rw [← hD.bruhatTitsGroupSchemes.neutral_points]
  exact (D.quotients.quotient Fa).positivePoints_le_integralPoints

/-- In particular it lies in `G(F)^0`. -/
theorem facetPositiveSubgroup_le_zeroSubgroup (hD : D.SatisfiesGroupAxioms) :
    facetPositiveSubgroup D Fa ≤ D.base.zeroSubgroup :=
  (facetPositiveSubgroup_le_facetZeroFixer D Fa hD).trans inf_le_right

/-- Under Axiom 4.1.22 the radical preimage is normal in the facet's zero fixer. -/
theorem facetPositiveSubgroup_normal_in_zeroFixer (hD : D.SatisfiesGroupAxioms) :
    ((facetPositiveSubgroup D Fa).subgroupOf (facetZeroFixer D Fa)).Normal := by
  change ((D.quotients.quotient Fa).positivePoints.subgroupOf
    (BuildingModelFamily.zeroFixer D.base (BuildingModelIndex.ofFacet Fa))).Normal
  rw [← hD.bruhatTitsGroupSchemes.neutral_points]
  exact (D.quotients.quotient Fa).positivePoints_subgroupOf_normal
    (hD.reductiveQuotients.facets.reductive_quotients Fa).2.1

/-- Positive subgroups grow along the facet order, by Axiom 4.1.22(7). -/
theorem facetPositiveSubgroup_le_of_precedes (hD : D.SatisfiesGroupAxioms)
    (Fb : BuildingFacet D.base.toValuationBuildingData)
    (h : FacetPrecedes D.base.toValuationBuildingData Fa Fb) :
    facetPositiveSubgroup D Fa ≤ facetPositiveSubgroup D Fb :=
  (hD.reductiveQuotients.facets.positive_radicals Fa Fb h).2.2

end Langlands.BruhatTits.MaximalProP
