import Langlands.BruhatTits.MaximalProP.AvailableChamberSplit
import Langlands.BruhatTits.Unipotent.CompactSubgroupsProP
import Langlands.GroupScheme.IntegralModel.LocalCompactPoints

/-! # Compact pro-p unipotent factors of apartment chamber fixers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels
  Langlands.AlgebraicGeometry.PointTopology Langlands.Cohomology
open Langlands.Geometry.Building.ParahoricBuildingData

namespace Langlands.BruhatTits.MaximalProP

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {D : KPBuildingDatum G}

local instance chamberUnipotentAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance chamberUnipotentPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- The actual pointwise zero fixer of a facet is compact, by its identification
with the neutral model's integral points. -/
theorem isCompact_facetZeroFixer (hD : D.SatisfiesGroupAxioms)
    (C : BuildingFacet D.base.toValuationBuildingData) :
    IsCompact (facetZeroFixer D C : Set (rationalPoints G)) := by
  change IsCompact (BuildingModelFamily.zeroFixer D.base (BuildingModelIndex.ofFacet C) :
    Set (rationalPoints G))
  rw [← hD.bruhatTitsGroupSchemes.neutral_points]
  exact (D.models.model (BuildingModelIndex.ofFacet C)).neutral.isCompact_integralPoints_localField

/-- Each actual dynamic unipotent factor of an apartment chamber fixer is compact.
No genericity assumption on the cocharacter is needed. -/
theorem isCompact_chamber_unipotent_factor (hD : D.SatisfiesGroupAxioms)
    {Ca : Set D.base.Apartment} (hCa : AffineRootSystem.IsChamber D.base.affineRoots Ca)
    (ν : cocharacterLattice D.base.S) :
    IsCompact (D.base.zeroStabilizerUnipotentPoints ν (D.base.apartmentMap '' Ca) :
      Set (rationalPoints G)) := by
  let : T2Space F := localField_t2Space F
  change IsCompact ((DynamicUnipotentContainment.unipotentPoints
    (CommGroupScheme.groupHom ν ≫ D.base.i) : Set (rationalPoints G)) ∩
    (D.base.zeroStabilizer (D.base.apartmentMap '' Ca) : Set (rationalPoints G)))
  rw [zeroStabilizer_eq_chamberFacetZeroFixer hD hCa]
  exact (isCompact_facetZeroFixer hD _).inter_left
    (DynamicUnipotentContainment.isClosed_unipotentPoints _)

/-- The original unipotent Iwahori factor is pro-p for the actual residue
characteristic, in its inherited rational-point topology. -/
theorem isProP_chamber_unipotent_factor (hD : D.SatisfiesGroupAxioms)
    {Ca : Set D.base.Apartment} (hCa : AffineRootSystem.IsChamber D.base.affineRoots Ca)
    (ν : cocharacterLattice D.base.S) :
    IsProPSubgroup (ringChar 𝓀[F])
      (D.base.zeroStabilizerUnipotentPoints ν (D.base.apartmentMap '' Ca)) := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  exact DynamicUnipotentContainment.isProPSubgroup_of_isCompact_le_unipotentPoints
    (CommGroupScheme.groupHom ν ≫ D.base.i) _
    (isCompact_chamber_unipotent_factor hD hCa ν) inf_le_left

/-- Choose actual positive and centralizer-zero factors without assuming the
pro-p property of either unipotent Iwahori factor. -/
def chamberPositiveCentralizerDecomposition
    (hD : D.SatisfiesGroupAxioms)
    {Ca : Set D.base.Apartment} (hCa : AffineRootSystem.IsChamber D.base.affineRoots Ca)
    (ν : cocharacterLattice D.base.S) (hν : IsGenericCocharacter D.base.i ν)
    (b : facetZeroFixer D (chamberFacet hCa.isFacet)) :
    {q : facetPositiveSubgroup D (chamberFacet hCa.isFacet) × D.base.centralizerZero //
      (b : rationalPoints G) = (q.1 : rationalPoints G) *
        rationalPoints.map D.base.centralizer.j (q.2 : rationalPoints D.base.centralizer.Z)} :=
  chamberPositiveCentralizerFactors hD hCa ν hν
    (isProP_chamber_unipotent_factor hD hCa ν)
    (isProP_chamber_unipotent_factor hD hCa (-ν)) b

/-- The positive subgroup of an apartment chamber has the chamber fixer as its
normalizer in the zero subgroup, under the single-group axioms alone. -/
theorem chamber_normalizer_eq
    (hD : D.SatisfiesGroupAxioms)
    {Ca : Set D.base.Apartment} (hCa : AffineRootSystem.IsChamber D.base.affineRoots Ca)
    (ν : cocharacterLattice D.base.S) (hν : IsGenericCocharacter D.base.i ν) :
    facetPositiveZeroNormalizer D (chamberFacet hCa.isFacet) =
      facetZeroFixer D (chamberFacet hCa.isFacet) :=
  chamber_normalizer_eq_of_unipotent_factors hD hCa ν hν
    (isProP_chamber_unipotent_factor hD hCa ν)
    (isProP_chamber_unipotent_factor hD hCa (-ν))

end Langlands.BruhatTits.MaximalProP
