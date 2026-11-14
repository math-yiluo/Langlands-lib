import Langlands.BruhatTits.MaximalProP.AvailableChamberUnipotent
import Langlands.GroupScheme.Rational.GenericCocharacter

/-! # Corrected KP Proposition 13.5.2 on available data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels
  Langlands.AlgebraicGeometry.PointTopology Langlands.Cohomology
  Langlands.Group.RelativeWeyl
open Langlands.Geometry.Building.ParahoricBuildingData

namespace Langlands.BruhatTits.MaximalProP

section Datum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {D : KPBuildingDatum G}

local instance availableProofPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- One apartment-chamber normalizer identity determines the identity for every
chamber by conjugation within the zero subgroup. -/
theorem chamber_normalizer_eq_of_one_apartment_chamber
    (hD : D.SatisfiesGroupAxioms)
    {Ca : Set D.base.Apartment} (hCa : AffineRootSystem.IsChamber D.base.affineRoots Ca)
    (ν : cocharacterLattice D.base.S) (hν : IsGenericCocharacter D.base.i ν)
    (hpos : IsProPSubgroup (ringChar 𝓀[F])
      (D.base.zeroStabilizerUnipotentPoints ν (D.base.apartmentMap '' Ca)))
    (hneg : IsProPSubgroup (ringChar 𝓀[F])
      (D.base.zeroStabilizerUnipotentPoints (-ν) (D.base.apartmentMap '' Ca)))
    (C : BuildingFacet D.base.toValuationBuildingData) (hC : D.base.IsChamber C.val) :
    Subgroup.normalizer (facetPositiveSubgroup D C : Set (rationalPoints G)) ⊓
      D.base.zeroSubgroup = facetZeroFixer D C := by
  let E : BuildingFacet D.base.toValuationBuildingData := chamberFacet hCa.isFacet
  have hE : D.base.IsChamber E.val := isChamber_chamberFacet hCa
  obtain ⟨g, hfix⟩ := exists_chamber_fixer_conjugator hD E C hE hC
  have hpositive := chamber_positive_eq_conjugate_of_zeroFixer_eq hD
    (facetReductiveComparisons hD) (isProP_facetPositiveSubgroup hD localFieldPositiveProP)
    E C hE hC g hfix
  have hN := chamber_normalizer_eq_of_unipotent_factors hD hCa ν hν hpos hneg
  change Subgroup.normalizer (facetPositiveSubgroup D E : Set (rationalPoints G)) ⊓
    D.base.zeroSubgroup = facetZeroFixer D E at hN
  let f : rationalPoints G →* rationalPoints G := MulAut.conj (g : rationalPoints G)
  have hzero : D.base.zeroSubgroup.map f = D.base.zeroSubgroup :=
    conjugateSubgroup_eq_self g.property
  have hmap := congrArg (Subgroup.map f) hN
  rw [Subgroup.map_inf _ _ f (MulAut.conj (g : rationalPoints G)).injective,
    Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj (g : rationalPoints G)).bijective,
    hzero] at hmap
  rw [hpositive, hfix]
  exact hmap

/-- The single-group datum axioms imply all four corrected conclusions. -/
theorem maximalProPConclusions_of_groupAxioms (hD : D.SatisfiesGroupAxioms) :
    MaximalProPConclusions D := by
  classical
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  have hA := hD.affineRootSystem.apartmentAxioms
  have hΨ := hA.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement
  obtain ⟨p, hp, -⟩ := hΨ.exists_regularPoint_closure (Classical.arbitrary D.base.Apartment)
  have hCa : AffineRootSystem.IsChamber D.base.affineRoots
      (AffineRootSystem.facet D.base.affineRoots p) := ⟨p, hp, rfl⟩
  obtain ⟨ν, hν⟩ := D.base.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter
    D.base.i
  exact maximalProPConclusions_of_chamberNormalizers hD
    (chamber_normalizer_eq_of_one_apartment_chamber hD hCa ν hν
      (isProP_chamber_unipotent_factor hD hCa ν)
      (isProP_chamber_unipotent_factor hD hCa (-ν)))

end Datum

/-- Corrected KP Proposition 13.5.2 for every available assignment, at an
arbitrary universe. -/
theorem availableMaximalProP : AvailableMaximalProPStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro 𝔅 h𝔅
  exact maximalProPConclusions_of_groupAxioms h𝔅.groupAxioms

end Langlands.BruhatTits.MaximalProP
