import Langlands.BruhatTits.MaximalProP.AvailableFixedFacet
import Langlands.Group.TitsAdmissibleSubparabolic

/-! # Compact overgroups of facet fixers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels
  Langlands.AlgebraicGeometry.PointTopology Langlands.Group Langlands.Group.TitsSystem

namespace Langlands.BruhatTits.MaximalProP

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {D : KPBuildingDatum G}

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- Setwise facet stabilizers in the zero subgroup map to the actual pointwise
facet fixers under the group axioms. -/
theorem map_facetZeroStabilizer_eq_facetZeroFixer (hD : D.SatisfiesGroupAxioms)
    (Fa : BuildingFacet D.base.toValuationBuildingData) :
    (D.base.facetZeroStabilizer Fa).map D.base.zeroSubgroup.subtype =
      facetZeroFixer D Fa := by
  have hA := hD.affineRootSystem.apartmentAxioms
  have hΨ := hA.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
  obtain ⟨p, hp, -⟩ := hΨ.exists_regularPoint_closure (Classical.arbitrary D.base.Apartment)
  obtain ⟨W, instW, π, Sgen, hT⟩ := hD.titsSystem _ ⟨p, hp, rfl⟩
  change (D.base.zeroStabilizerIn Fa.val).map D.base.zeroSubgroup.subtype = _
  rw [D.base.map_zeroStabilizerIn]
  ext g
  constructor
  · intro hg
    refine ⟨?_, hg.1⟩
    intro y
    exact D.base.facetZeroStabilizer_smul_eq hA
      hD.building.normalizerApartmentStabilizer
      hD.affineRootSystem.compatibleApartmentFacets hT Fa ⟨g, hg.1⟩ hg.2 y.property
  · rintro ⟨hfix, hg0⟩
    refine ⟨hg0, ?_⟩
    change g • Fa.val = Fa.val
    ext y
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [hfix ⟨x, hx⟩] using hx
    · intro hy
      exact ⟨y, hy, hfix ⟨y, hy⟩⟩

/-- Under the group axioms, distinct building facets have distinct pointwise
fixers in the zero subgroup. -/
theorem facetZeroFixer_injective (hD : D.SatisfiesGroupAxioms) :
    Function.Injective (facetZeroFixer D) := by
  have hA := hD.affineRootSystem.apartmentAxioms
  have hΨ := hA.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
  obtain ⟨p, hp, -⟩ := hΨ.exists_regularPoint_closure (Classical.arbitrary D.base.Apartment)
  obtain ⟨W, instW, π, Sgen, hT⟩ := hD.titsSystem _ ⟨p, hp, rfl⟩
  intro Fa Fb heq
  apply hT.bijOn_facetZeroStabilizer.injOn (Set.mem_univ Fa) (Set.mem_univ Fb)
  apply Subgroup.map_injective D.base.zeroSubgroup.subtype_injective
  simpa only [map_facetZeroStabilizer_eq_facetZeroFixer hD] using heq

/-- A compact subgroup of the zero subgroup containing a facet fixer is the
fixer of a face of that facet. -/
theorem exists_facetZeroFixer_eq_of_isCompact (hD : D.SatisfiesGroupAxioms)
    (C : BuildingFacet D.base.toValuationBuildingData)
    (H : Subgroup (rationalPoints G)) (hH0 : H ≤ D.base.zeroSubgroup)
    (hH : IsCompact (H : Set (rationalPoints G))) (hCH : facetZeroFixer D C ≤ H) :
    ∃ Fa : BuildingFacet D.base.toValuationBuildingData,
      H = facetZeroFixer D Fa ∧ FacetPrecedes D.base.toValuationBuildingData Fa C := by
  obtain ⟨Fq, hHFq⟩ := exists_le_facetZeroFixer_of_isCompact hD H hH0 hH
  have hA := hD.affineRootSystem.apartmentAxioms
  have hΨ := hA.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
  obtain ⟨p, hp, -⟩ := hΨ.exists_regularPoint_closure (Classical.arbitrary D.base.Apartment)
  obtain ⟨W, instW, π, Sgen, hT⟩ := hD.titsSystem _ ⟨p, hp, rfl⟩
  have hCH' : D.base.facetZeroStabilizer C ≤ H.subgroupOf D.base.zeroSubgroup :=
    (Subgroup.map_le_map_iff_of_injective D.base.zeroSubgroup.subtype_injective).mp (by
      rw [map_facetZeroStabilizer_eq_facetZeroFixer hD,
        Subgroup.map_subgroupOf_eq_of_le hH0]
      exact hCH)
  have hHQ : H.subgroupOf D.base.zeroSubgroup ≤ D.base.facetZeroStabilizer Fq :=
    (Subgroup.map_le_map_iff_of_injective D.base.zeroSubgroup.subtype_injective).mp (by
      rw [map_facetZeroStabilizer_eq_facetZeroFixer hD,
        Subgroup.map_subgroupOf_eq_of_le hH0]
      exact hHFq)
  have hpar : IsParabolic
      (D.base.chamberZeroStabilizerIn (AffineRootSystem.facet D.base.affineRoots p))
      (H.subgroupOf D.base.zeroSubgroup) := by
    obtain ⟨g, hg⟩ := hT.isParabolic_facetZeroStabilizer C
    exact ⟨g, hg.trans hCH'⟩
  have hadm := hT.isTitsSystem.isAdmissibleParabolic_of_le hpar
    (hT.bijOn_facetZeroStabilizer.mapsTo (Set.mem_univ Fq)) hHQ
  obtain ⟨Fa, hFa⟩ := hT.exists_facetZeroStabilizer_eq hadm
  have heq := congrArg (Subgroup.map D.base.zeroSubgroup.subtype) hFa
  rw [map_facetZeroStabilizer_eq_facetZeroFixer hD,
    Subgroup.map_subgroupOf_eq_of_le hH0] at heq
  refine ⟨Fa, heq.symm, (hT.facetPrecedes_iff Fa C).mpr ?_⟩
  rwa [hFa]

/-- Choose the face whose fixer is a given compact overgroup of a facet
fixer, retaining both the equality and incidence. -/
def compactOvergroupFacet (hD : D.SatisfiesGroupAxioms)
    (C : BuildingFacet D.base.toValuationBuildingData)
    (H : Subgroup (rationalPoints G)) (hH0 : H ≤ D.base.zeroSubgroup)
    (hH : IsCompact (H : Set (rationalPoints G))) (hCH : facetZeroFixer D C ≤ H) :
    { Fa : BuildingFacet D.base.toValuationBuildingData //
      H = facetZeroFixer D Fa ∧ FacetPrecedes D.base.toValuationBuildingData Fa C } :=
  ⟨Classical.choose (exists_facetZeroFixer_eq_of_isCompact hD C H hH0 hH hCH),
    Classical.choose_spec (exists_facetZeroFixer_eq_of_isCompact hD C H hH0 hH hCH)⟩

end Langlands.BruhatTits.MaximalProP
