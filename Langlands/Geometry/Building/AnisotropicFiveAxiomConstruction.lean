import Langlands.Geometry.Building.AnisotropicApartmentSplitting
import Langlands.Geometry.Building.RootFreeApartmentConstruction
import Langlands.GroupScheme.Rational.AnisotropicCentralizerNormKernel
import Langlands.BruhatTits.RationalPoints.BoundedSetOperations

/-! # All five metric-construction axiom families on supplied anisotropic data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Plancherel
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- On supplied anisotropic data, the actual norm-one point stabilizer is the entire
rational-point group, for every original quotient point. -/
theorem compactStabilizer_eq_top_of_isAnisotropic
    (hG : IsAnisotropic G) (y : B.ReducedBuilding) : B.compactStabilizer y = ⊤ := by
  have hB := B.apartment.subsingleton_reducedBuilding_of_isAnisotropic hG
    B.isMaximalSplitTorus.isSplitSubtorus
  apply top_unique
  intro g _
  apply B.mem_compactStabilizer.mpr
  refine ⟨?_, hB.elim _ _⟩
  rw [hG.rationalCommonNormKernel_eq_top B.isConnectedReductive]
  exact Subgroup.mem_top _

/-- KP Axiom 4.1.2 holds in the exact canonical rational-point topology, from
published compactness of an actual anisotropic connected reductive group. -/
theorem hasBoundedOpenStabilizers_of_isAnisotropic (hG : IsAnisotropic G) :
    B.HasBoundedOpenStabilizers := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  change ∀ y : B.ReducedBuilding,
    IsOpen (B.compactStabilizer y : Set (rationalPoints G)) ∧
      IsAlgebraicallyBounded F G.X (B.compactStabilizer y : Set (rationalPoints G))
  intro y
  rw [B.compactStabilizer_eq_top_of_isAnisotropic hG y]
  simp only [Subgroup.coe_top]
  exact ⟨isOpen_univ, isAlgebraicallyBounded_of_isCompact
    ((anisotropicCompactness_proof F G B.isConnectedReductive).mpr hG)⟩

/-- There are no actual root-indexed reflection cases on anisotropic data. -/
theorem hasRootReflections_of_isAnisotropic (hG : IsAnisotropic G) :
    B.HasRootReflections := by
  have : IsEmpty (relativeRoots B.i) := Set.isEmpty_coe_sort.2
    (hG.relativeRoots_eq_empty B.isMaximalSplitTorus.isSplitSubtorus)
  intro α
  exact isEmptyElim α

/-- V 6, V 7 and AS 2–AS 5 for the actual anisotropic apartment. -/
theorem satisfiesApartmentAxioms_of_isAnisotropic (hG : IsAnisotropic G) :
    B.SatisfiesApartmentAxioms :=
  B.apartment.satisfiesApartmentAxioms_of_relativeRoots_eq_empty B.centralizer
    (hG.relativeRoots_eq_empty B.isMaximalSplitTorus.isSplitSubtorus)

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- Explicit realization and splitting with precisely the seven predicates representing
the five metric-construction axiom families, on supplied actual anisotropic data. -/
def anisotropicFiveAxiomData (hG : IsAnisotropic G) :
    {RT : P.toValuationBuildingData.PolysimplicialRealization ×
        P.toValuationBuildingData.ApartmentSplitting //
      P.SatisfiesBuildingAxiom RT.1 ∧
      P.HasBoundedOpenStabilizers ∧
      P.SatisfiesAffineApartmentAxiom RT.2 ∧
      P.HasRootReflections ∧
      P.SatisfiesApartmentAxioms ∧
      P.HasCompatibleApartmentFacets ∧
      P.HasTitsSystem} :=
  ⟨⟨P.toValuationBuildingData.anisotropicRealization hG,
      P.anisotropicApartmentSplitting hG⟩,
    P.toValuationBuildingData.satisfiesBuildingAxiom_anisotropicRealization hG,
    P.toValuationBuildingData.hasBoundedOpenStabilizers_of_isAnisotropic hG,
    P.satisfiesAffineApartmentAxiom_anisotropicApartmentSplitting hG,
    P.toValuationBuildingData.hasRootReflections_of_isAnisotropic hG,
    P.toValuationBuildingData.satisfiesApartmentAxioms_of_isAnisotropic hG,
    P.toValuationBuildingData.hasCompatibleApartmentFacets_of_relativeRoots_eq_empty
      (hG.relativeRoots_eq_empty P.isMaximalSplitTorus.isSplitSubtorus),
    P.hasTitsSystem_of_isAnisotropic hG⟩

end ParahoricBuildingData

end Langlands.Geometry.Building
