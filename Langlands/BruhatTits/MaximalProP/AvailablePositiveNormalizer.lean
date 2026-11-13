import Langlands.BruhatTits.MaximalProP.AvailableCompactOvergroup
import Langlands.BruhatTits.MaximalProP.FacetPositiveTopology
import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Positive normalizers as facet fixers under an explicit boundedness input -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels
  Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.MaximalProP

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {D : KPBuildingDatum G}

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- The normalizer of the actual facet radical preimage inside `G(F)^0`. -/
def facetPositiveZeroNormalizer (D : KPBuildingDatum G)
    (Fa : BuildingFacet D.base.toValuationBuildingData) : Subgroup (rationalPoints G) :=
  Subgroup.normalizer (facetPositiveSubgroup D Fa : Set (rationalPoints G)) ⊓
    D.base.zeroSubgroup

/-- The facet fixer normalizes its positive subgroup. -/
theorem facetZeroFixer_le_facetPositiveZeroNormalizer (hD : D.SatisfiesGroupAxioms)
    (Fa : BuildingFacet D.base.toValuationBuildingData) :
    facetZeroFixer D Fa ≤ facetPositiveZeroNormalizer D Fa := by
  apply le_inf
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (facetPositiveSubgroup_le_facetZeroFixer D Fa hD)).mp
        (facetPositiveSubgroup_normal_in_zeroFixer D Fa hD)
  · exact inf_le_right

/-- The positive normalizer in the zero subgroup is open in the ambient point topology. -/
theorem isOpen_facetPositiveZeroNormalizer (hD : D.SatisfiesGroupAxioms)
    (Fa : BuildingFacet D.base.toValuationBuildingData) :
    IsOpen (facetPositiveZeroNormalizer D Fa : Set (rationalPoints G)) := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  exact Subgroup.isOpen_mono
    ((facetPositiveSubgroup_le_facetZeroFixer D Fa hD).trans
      (facetZeroFixer_le_facetPositiveZeroNormalizer hD Fa))
    (isOpen_facetPositiveSubgroup D Fa)

/-- The same subgroup is closed, since every open subgroup is closed. -/
theorem isClosed_facetPositiveZeroNormalizer (hD : D.SatisfiesGroupAxioms)
    (Fa : BuildingFacet D.base.toValuationBuildingData) :
    IsClosed (facetPositiveZeroNormalizer D Fa : Set (rationalPoints G)) := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  exact Subgroup.isClosed_of_isOpen _ (isOpen_facetPositiveZeroNormalizer hD Fa)

/-- Boundedness of the normalizer in the rational norm kernel implies compactness
of its intersection with the zero subgroup. -/
theorem isCompact_facetPositiveZeroNormalizer (hD : D.SatisfiesGroupAxioms)
    (Fa : BuildingFacet D.base.toValuationBuildingData)
    (hb : IsAlgebraicallyBounded F G.X
      ((Subgroup.normalizer (facetPositiveSubgroup D Fa : Set (rationalPoints G)) ⊓
        Langlands.Plancherel.rationalCommonNormKernel G) : Set (rationalPoints G))) :
    IsCompact (facetPositiveZeroNormalizer D Fa : Set (rationalPoints G)) := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  apply (localFieldAffineBoundedCompactness_proof F G.X _
    (isClosed_facetPositiveZeroNormalizer hD Fa)).mp
  intro f
  obtain ⟨b, hb0, hbf⟩ := hb f
  refine ⟨b, hb0, fun g hg => hbf g ?_⟩
  exact ⟨hg.1, D.base.zeroDatum.zeroSubgroup_le_rationalCommonNormKernel hg.2⟩

/-- Choose a face of the given facet whose zero fixer is exactly its positive
normalizer in the zero subgroup, assuming boundedness in the rational norm kernel. -/
def positiveNormalizerFacet (hD : D.SatisfiesGroupAxioms)
    (Fa : BuildingFacet D.base.toValuationBuildingData)
    (hb : IsAlgebraicallyBounded F G.X
      ((Subgroup.normalizer (facetPositiveSubgroup D Fa : Set (rationalPoints G)) ⊓
        Langlands.Plancherel.rationalCommonNormKernel G) : Set (rationalPoints G))) :
    { Fb : BuildingFacet D.base.toValuationBuildingData //
      facetPositiveZeroNormalizer D Fa = facetZeroFixer D Fb ∧
        FacetPrecedes D.base.toValuationBuildingData Fb Fa } :=
  compactOvergroupFacet hD Fa (facetPositiveZeroNormalizer D Fa) inf_le_right
    (isCompact_facetPositiveZeroNormalizer hD Fa hb)
    (facetZeroFixer_le_facetPositiveZeroNormalizer hD Fa)

end Langlands.BruhatTits.MaximalProP
