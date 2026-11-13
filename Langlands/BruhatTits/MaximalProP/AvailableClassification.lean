import Langlands.BruhatTits.MaximalProP.AvailableChamberMaximality
import Langlands.BruhatTits.MaximalProP.AvailableMaximalClassification
import Langlands.BruhatTits.MaximalProP.AvailableMaximalFacetChamber
import Langlands.BruhatTits.MaximalProP.FacetRadicalPreimage
import Langlands.BruhatTits.IntegralModels.PositiveProP
import Langlands.GroupScheme.Rational.FiniteFieldBorelSylow

/-! # Maximal open pro-p classification on available data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels
  Langlands.AlgebraicGeometry.PointTopology Langlands.Cohomology

namespace Langlands.BruhatTits.MaximalProP

section Datum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {D : KPBuildingDatum G}

local instance completeClassificationPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- Every actual facet positive subgroup is open pro-p and lies in the actual
zero subgroup, using the single-group axioms alone. -/
theorem facetPositive_openProP (hD : D.SatisfiesGroupAxioms)
    (Fa : BuildingFacet D.base.toValuationBuildingData) :
    facetPositiveSubgroup D Fa ≤ D.base.zeroSubgroup ∧
      IsOpen (facetPositiveSubgroup D Fa : Set (rationalPoints G)) ∧
      IsProPSubgroup (ringChar 𝓀[F]) (facetPositiveSubgroup D Fa) := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  exact ⟨facetPositiveSubgroup_le_zeroSubgroup D Fa hD,
    isOpen_facetPositiveSubgroup D Fa,
    isProP_facetPositiveSubgroup hD localFieldPositiveProP Fa⟩

/-- The positive subgroup of a facet is maximal open pro-p in the zero
subgroup exactly when that same facet is a chamber. -/
theorem facetPositive_maximal_iff_isChamber (hD : D.SatisfiesGroupAxioms)
    (Fa : BuildingFacet D.base.toValuationBuildingData) :
    IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup
      (facetPositiveSubgroup D Fa) ↔ D.base.IsChamber Fa.val := by
  have hcomp := facetReductiveComparisons hD
  have hpos := isProP_facetPositiveSubgroup hD localFieldPositiveProP
  exact ⟨isChamber_of_maximal_facetPositive hD hcomp
      finiteFieldNormalSylowTorus Fa (hpos Fa),
    isMaximalOpenProPIn_chamber hD hcomp finiteFieldSylowBorel hpos Fa⟩

/-- Every maximal open pro-p subgroup of the zero subgroup is the actual
positive subgroup of a chamber, with no structural theorem premises. -/
theorem exists_chamber_positive_eq (hD : D.SatisfiesGroupAxioms)
    (H : Subgroup (rationalPoints G))
    (hH : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup H) :
    ∃ C : BuildingFacet D.base.toValuationBuildingData,
      D.base.IsChamber C.val ∧ H = facetPositiveSubgroup D C :=
  exists_chamber_of_isMaximalOpenProP hD (facetReductiveComparisons hD)
    finiteFieldSylowBorel localFieldPositiveProP H hH

/-- Choose a chamber representing a maximal open pro-p subgroup, retaining its
literal equality to that chamber's positive subgroup. -/
def maximalOpenProPRepresentative (hD : D.SatisfiesGroupAxioms)
    (H : Subgroup (rationalPoints G))
    (hH : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup H) :
    {C : BuildingFacet D.base.toValuationBuildingData //
      D.base.IsChamber C.val ∧ H = facetPositiveSubgroup D C} :=
  ⟨(exists_chamber_positive_eq hD H hH).choose,
    (exists_chamber_positive_eq hD H hH).choose_spec⟩

/-- The actual positive subgroup of a chamber, equipped with its maximality
certificate. -/
def chamberMaximalProPSubgroup (hD : D.SatisfiesGroupAxioms)
    (C : {C : BuildingFacet D.base.toValuationBuildingData //
      D.base.IsChamber C.val}) :
    {H : Subgroup (rationalPoints G) //
      IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup H} :=
  ⟨facetPositiveSubgroup D C.val,
    (facetPositive_maximal_iff_isChamber hD C.val).mpr C.property⟩

@[simp] theorem chamberMaximalProPSubgroup_val (hD : D.SatisfiesGroupAxioms)
    (C : {C : BuildingFacet D.base.toValuationBuildingData //
      D.base.IsChamber C.val}) :
    (chamberMaximalProPSubgroup hD C).val = facetPositiveSubgroup D C.val := rfl

/-- Chambers map onto all maximal open pro-p subgroups of the zero subgroup. -/
theorem chamberMaximalProPSubgroup_surjective (hD : D.SatisfiesGroupAxioms) :
    Function.Surjective (chamberMaximalProPSubgroup hD) := by
  rintro ⟨H, hH⟩
  let C := maximalOpenProPRepresentative hD H hH
  refine ⟨⟨C.val, C.property.1⟩, ?_⟩
  exact Subtype.ext C.property.2.symm

/-- After the classification, only the direct chamber-normalizer identities
remain to establish all four corrected KP conclusions. -/
theorem maximalProPConclusions_of_chamberNormalizers (hD : D.SatisfiesGroupAxioms)
    (hN : ∀ C : BuildingFacet D.base.toValuationBuildingData,
      D.base.IsChamber C.val →
      Subgroup.normalizer (facetPositiveSubgroup D C : Set (rationalPoints G)) ⊓
        D.base.zeroSubgroup = facetZeroFixer D C) :
    MaximalProPConclusions D :=
  ⟨facetPositive_openProP hD, facetPositive_maximal_iff_isChamber hD,
    exists_chamber_positive_eq hD, hN⟩

end Datum

end Langlands.BruhatTits.MaximalProP
