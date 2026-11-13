import Langlands.BruhatTits.MaximalProP.AvailableStatement
import Langlands.Geometry.Building.BoundedSubgroupFixedPointProof
import Langlands.Geometry.Building.BuildingFacetPartition

/-! # Compact subgroups fix facets on available Bruhat–Tits data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels
  Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.MaximalProP

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {D : KPBuildingDatum G}

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- A compact subgroup fixes a point of the reduced building. Only the
single-group axioms of availability are used. -/
theorem exists_fixed_point_of_isCompact (hD : D.SatisfiesGroupAxioms)
    (H : Subgroup (rationalPoints G)) (hH : IsCompact (H : Set (rationalPoints G))) :
    ∃ x : D.base.ReducedBuilding, ∀ g ∈ H, g • x = x := by
  let : T2Space F := by
    let := IsTopologicalAddGroup.rightUniformSpace F
    let := isUniformAddGroup_of_addCommGroup (G := F)
    infer_instance
  let := rationalPoint_t2Space F G
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  have hb : IsAlgebraicallyBounded F G.X (H : Set (rationalPoints G)) :=
    (localFieldAffineBoundedCompactness_proof F G.X _ hH.isClosed).mpr hH
  exact (boundedSubgroupFixedPoint F G D.base.isConnectedReductive D.base D.realization
    D.splitting hD.building hD.boundedSubgroups hD.affineStructure
    hD.affineRootSystem.rootReflections hD.affineRootSystem.apartmentAxioms
    hD.affineRootSystem.compatibleApartmentFacets hD.titsSystem H hb).1

/-- A subgroup of the zero subgroup fixing a point fixes its containing
facet pointwise. -/
theorem le_facetZeroFixer_of_fixed_point (hD : D.SatisfiesGroupAxioms)
    (H : Subgroup (rationalPoints G)) (hH0 : H ≤ D.base.zeroSubgroup)
    (x : D.base.ReducedBuilding) (hx : ∀ g ∈ H, g • x = x) :
    H ≤ facetZeroFixer D (D.base.toValuationBuildingData.buildingFacetAt x) := by
  have hA := hD.affineRootSystem.apartmentAxioms
  have hΨ := hA.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
  obtain ⟨p, hp, -⟩ := hΨ.exists_regularPoint_closure (Classical.arbitrary D.base.Apartment)
  obtain ⟨W, instW, π, Sgen, hT⟩ := hD.titsSystem _ ⟨p, hp, rfl⟩
  intro g hg
  refine ⟨?_, hH0 hg⟩
  intro y
  have hset :
      g • (D.base.toValuationBuildingData.buildingFacetAt x).val =
        (D.base.toValuationBuildingData.buildingFacetAt x).val := by
    rw [← D.base.toValuationBuildingData.buildingFacetAt_smul hA g x, hx g hg]
  exact D.base.facetZeroStabilizer_smul_eq hA hD.building.normalizerApartmentStabilizer
    hD.affineRootSystem.compatibleApartmentFacets hT
    (D.base.toValuationBuildingData.buildingFacetAt x) ⟨g, hH0 hg⟩ hset y.property

/-- Every compact subgroup of the zero subgroup lies in a facet fixer. -/
theorem exists_le_facetZeroFixer_of_isCompact (hD : D.SatisfiesGroupAxioms)
    (H : Subgroup (rationalPoints G)) (hH0 : H ≤ D.base.zeroSubgroup)
    (hH : IsCompact (H : Set (rationalPoints G))) :
    ∃ Fa : BuildingFacet D.base.toValuationBuildingData, H ≤ facetZeroFixer D Fa := by
  obtain ⟨x, hx⟩ := exists_fixed_point_of_isCompact hD H hH
  exact ⟨_, le_facetZeroFixer_of_fixed_point hD H hH0 x hx⟩

/-- A choice of a facet fixed pointwise by a compact subgroup of the zero
subgroup, bundled with its containment property. -/
def compactSubgroupFixedFacet (hD : D.SatisfiesGroupAxioms)
    (H : Subgroup (rationalPoints G)) (hH0 : H ≤ D.base.zeroSubgroup)
    (hH : IsCompact (H : Set (rationalPoints G))) :
    { Fa : BuildingFacet D.base.toValuationBuildingData // H ≤ facetZeroFixer D Fa } :=
  ⟨Classical.choose (exists_le_facetZeroFixer_of_isCompact hD H hH0 hH),
    Classical.choose_spec (exists_le_facetZeroFixer_of_isCompact hD H hH0 hH)⟩

/-- In particular, a pro-`p` subgroup of the zero subgroup lies in a facet fixer. -/
theorem exists_le_facetZeroFixer_of_isProP (hD : D.SatisfiesGroupAxioms)
    {p : ℕ} (H : Subgroup (rationalPoints G)) (hH0 : H ≤ D.base.zeroSubgroup)
    (hH : Langlands.Cohomology.IsProPSubgroup p H) :
    ∃ Fa : BuildingFacet D.base.toValuationBuildingData, H ≤ facetZeroFixer D Fa := by
  let := hH.compactSpace
  exact exists_le_facetZeroFixer_of_isCompact hD H hH0
    (isCompact_iff_compactSpace.mpr inferInstance)

end Langlands.BruhatTits.MaximalProP
