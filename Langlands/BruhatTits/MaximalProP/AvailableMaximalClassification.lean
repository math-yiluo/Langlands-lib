import Langlands.BruhatTits.MaximalProP.AvailableFacetInputs
import Langlands.BruhatTits.MaximalProP.AvailableChamberDomination

/-! # Chambers representing maximal open pro-p subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels
  Langlands.AlgebraicGeometry.PointTopology Langlands.Cohomology

namespace Langlands.BruhatTits.MaximalProP

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {D : KPBuildingDatum G}

local instance classificationAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance classificationPointTopology : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- Maximality turns containment in a chamber positive subgroup into equality.
The finite-field, comparison and local-model theorem inputs remain explicit. -/
theorem exists_chamber_of_isMaximalOpenProP
    (hD : D.SatisfiesGroupAxioms) (hcomp : FacetReductiveComparisons D)
    (hSylow : FiniteFieldSylowBorelStatement.{u})
    (hpositive : LocalFieldPositiveProPStatement.{u})
    (H : Subgroup (rationalPoints G))
    (hH : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup H) :
    ∃ C : BuildingFacet D.base.toValuationBuildingData,
      D.base.IsChamber C.val ∧ H = facetPositiveSubgroup D C := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  obtain ⟨C, hC, hHC⟩ := exists_chamber_positive_ge_of_isProP
    hD hcomp hSylow H hH.1 hH.2.2.1
  exact ⟨C, hC, (hH.2.2.2 _ hHC
    (facetPositiveSubgroup_le_zeroSubgroup D C hD)
    (isOpen_facetPositiveSubgroup D C)
    (isProP_facetPositiveSubgroup hD hpositive C)).symm⟩

/-- Equal maximal facet positive subgroups determine the same facet via their
zero normalizers and injectivity of actual facet zero fixers. -/
theorem eq_of_facetPositiveSubgroup_eq_of_isMaximalOpenProP
    (hD : D.SatisfiesGroupAxioms) (hcomp : FacetReductiveComparisons D)
    (hnormal : FiniteFieldNormalSylowTorusStatement.{u})
    (hpositive : LocalFieldPositiveProPStatement.{u})
    (hbounded : RationalPoints.BoundedOpenNormalizerStatement.{u})
    (C E : BuildingFacet D.base.toValuationBuildingData)
    (hC : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup
      (facetPositiveSubgroup D C))
    (heq : facetPositiveSubgroup D C = facetPositiveSubgroup D E) : C = E := by
  have hE : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup
      (facetPositiveSubgroup D E) := heq ▸ hC
  have hCN := (isChamber_and_normalizer_eq_of_maximal_from_inputs
    hD hcomp hnormal hpositive hbounded C hC).2
  have hEN := (isChamber_and_normalizer_eq_of_maximal_from_inputs
    hD hcomp hnormal hpositive hbounded E hE).2
  apply facetZeroFixer_injective hD
  rw [← hCN, ← hEN]
  exact congrArg (fun K : Subgroup (rationalPoints G) =>
    Subgroup.normalizer (K : Set (rationalPoints G)) ⊓ D.base.zeroSubgroup) heq

/-- Every maximal open pro-p subgroup determines a unique chamber, under the
explicit structural inputs used by domination and the normalizer argument. -/
theorem existsUnique_chamber_of_isMaximalOpenProP
    (hD : D.SatisfiesGroupAxioms) (hcomp : FacetReductiveComparisons D)
    (hSylow : FiniteFieldSylowBorelStatement.{u})
    (hnormal : FiniteFieldNormalSylowTorusStatement.{u})
    (hpositive : LocalFieldPositiveProPStatement.{u})
    (hbounded : RationalPoints.BoundedOpenNormalizerStatement.{u})
    (H : Subgroup (rationalPoints G))
    (hH : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup H) :
    ∃! C : BuildingFacet D.base.toValuationBuildingData,
      D.base.IsChamber C.val ∧ H = facetPositiveSubgroup D C := by
  obtain ⟨C, hC, hHC⟩ := exists_chamber_of_isMaximalOpenProP hD hcomp hSylow hpositive H hH
  refine ⟨C, ⟨hC, hHC⟩, ?_⟩
  rintro E ⟨_, hHE⟩
  exact eq_of_facetPositiveSubgroup_eq_of_isMaximalOpenProP
    hD hcomp hnormal hpositive hbounded E C (hHE ▸ hH) (hHE.symm.trans hHC)

/-- Choose the chamber representing a maximal open pro-p subgroup, retaining
its subgroup equality and the ambient zero-normalizer identity. -/
def maximalOpenProPChamber
    (hD : D.SatisfiesGroupAxioms) (hcomp : FacetReductiveComparisons D)
    (hSylow : FiniteFieldSylowBorelStatement.{u})
    (hnormal : FiniteFieldNormalSylowTorusStatement.{u})
    (hpositive : LocalFieldPositiveProPStatement.{u})
    (hbounded : RationalPoints.BoundedOpenNormalizerStatement.{u})
    (H : Subgroup (rationalPoints G))
    (hH : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup H) :
    {C : BuildingFacet D.base.toValuationBuildingData // D.base.IsChamber C.val ∧
      H = facetPositiveSubgroup D C ∧
      Subgroup.normalizer (H : Set (rationalPoints G)) ⊓ D.base.zeroSubgroup =
        facetZeroFixer D C} := by
  let C := Classical.choose
    (exists_chamber_of_isMaximalOpenProP hD hcomp hSylow hpositive H hH)
  have hC := (Classical.choose_spec
    (exists_chamber_of_isMaximalOpenProP hD hcomp hSylow hpositive H hH)).1
  have hHC := (Classical.choose_spec
    (exists_chamber_of_isMaximalOpenProP hD hcomp hSylow hpositive H hH)).2
  refine ⟨C, hC, hHC, ?_⟩
  rw [hHC]
  exact (isChamber_and_normalizer_eq_of_maximal_from_inputs
    hD hcomp hnormal hpositive hbounded C (hHC ▸ hH)).2

end Langlands.BruhatTits.MaximalProP
