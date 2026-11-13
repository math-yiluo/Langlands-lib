import Langlands.BruhatTits.MaximalProP.AvailableChamberDomination
import Langlands.BruhatTits.MaximalProP.AvailableChamberConjugacy
import Langlands.BruhatTits.MaximalProP.FacetPositiveTopology
import Langlands.GroupScheme.Rational.TorusPointsPSubgroups
import Langlands.Geometry.Building.TitsRealizationChambers
import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.GroupTheory.SubgroupConjugation

/-! # Maximality of positive subgroups of chambers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels
  Langlands.AlgebraicGeometry.PointTopology Langlands.Cohomology
open Langlands.Group.RelativeWeyl MeasureTheory

namespace Langlands.BruhatTits.MaximalProP

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {D : KPBuildingDatum G}

local instance chamberMaximalityAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance chamberMaximalityPointTopology : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance chamberMaximalityTopologicalGroup [LocallyOfFiniteType G.X.hom] : IsTopologicalGroup (rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G
local instance chamberMaximalityLocallyCompact [LocallyOfFiniteType G.X.hom] : LocallyCompactSpace (rationalPoints G) :=
  rationalPoint_locallyCompactSpace F G
local instance chamberMaximalityT2 : T2Space (rationalPoints G) := rationalPoint_t2Space F G

/-- The published determinant argument proves unimodularity of the actual
rational-point group without a cocharacter parameter. -/
theorem rationalPoints_modularCharacter_eq_one [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) (g : rationalPoints G) :
    Measure.modularCharacter g = 1 := by
  let : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of F F)) :=
    G.affinePointsTopologicalSpace (CommAlgCat.of F F)
  let e := Langlands.Aubert.General.RationalPointFamily.rationalPointContinuousMulEquiv F G
  let : IsTopologicalGroup (G.affinePoints (CommAlgCat.of F F)) :=
    G.affinePointsIsTopologicalGroup (CommAlgCat.of F F)
  let : LocallyCompactSpace (G.affinePoints (CommAlgCat.of F F)) :=
    e.symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let : T2Space (G.affinePoints (CommAlgCat.of F F)) :=
    e.symm.toHomeomorph.isEmbedding.t2Space
  have hdet : Lie.adjointDeterminantCharacter G = 0 :=
    Lie.connectedReductiveAdjointDeterminant_of_centralDerivedProduct
      reductiveCentralDerivedProduct F G hG
  rw [← Langlands.Aubert.General.modularCharacter_continuousMulEquiv e g]
  exact Langlands.Aubert.General.RationalPointFamily.affinePoints_modularCharacter_eq_one
    F G hG.smooth hdet (e g)

/-- Every pro-p subgroup of a chamber fixer lies in its positive subgroup. -/
theorem le_chamber_positive_of_isProP
    (hD : D.SatisfiesGroupAxioms) (hcomp : FacetReductiveComparisons D)
    (C : BuildingFacet D.base.toValuationBuildingData) (hC : D.base.IsChamber C.val)
    (H : Subgroup (rationalPoints G)) (hH : IsProPSubgroup (ringChar 𝓀[F]) H)
    (hHC : H ≤ facetZeroFixer D C) : H ≤ facetPositiveSubgroup D C := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  let Q := D.quotients.quotient C
  let I := (D.models.facetModels.model C).neutral.integralPoints
  let : Fact (ringChar 𝓀[F]).Prime := ⟨hH.prime⟩
  have hHI : H ≤ I := by
    change H ≤ (D.models.model (BuildingModelIndex.ofFacet C)).neutral.integralPoints
    rw [hD.bruhatTitsGroupSchemes.neutral_points]
    exact hHC
  have himage : (H.subgroupOf I).map Q.parahoricReduction = ⊥ :=
    eq_bot_of_isPGroup_of_isTorus (ringChar 𝓀[F]) ((hcomp.1 C).mpr hC) _
      (Q.localField_isPGroup_reductionImage hH hHI)
  intro x hx
  have hred : Q.parahoricReduction (⟨x, hHI hx⟩ : I) = 1 := by
    have hm : Q.parahoricReduction (⟨x, hHI hx⟩ : I) ∈
        (H.subgroupOf I).map Q.parahoricReduction :=
      ⟨⟨x, hHI hx⟩, hx, rfl⟩
    rwa [himage, Subgroup.mem_bot] at hm
  have hk : (⟨x, hHI hx⟩ : I) ∈ Q.parahoricReduction.ker := hred
  rw [Q.ker_parahoricReduction
    (hD.reductiveQuotients.facets.reductive_quotients C).2.1] at hk
  exact hk

/-- A conjugacy between chamber fixers induces the same conjugacy between their
positive subgroups, using their largest-pro-p property. -/
theorem chamber_positive_eq_conjugate_of_zeroFixer_eq
    (hD : D.SatisfiesGroupAxioms) (hcomp : FacetReductiveComparisons D)
    (hpos : ∀ Fa, IsProPSubgroup (ringChar 𝓀[F]) (facetPositiveSubgroup D Fa))
    (C E : BuildingFacet D.base.toValuationBuildingData)
    (hC : D.base.IsChamber C.val) (hE : D.base.IsChamber E.val)
    (g : rationalPoints G)
    (hfix : facetZeroFixer D E = conjugateSubgroup g (facetZeroFixer D C)) :
    facetPositiveSubgroup D E = conjugateSubgroup g (facetPositiveSubgroup D C) := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  have hle : conjugateSubgroup g (facetPositiveSubgroup D C) ≤
      facetPositiveSubgroup D E :=
    le_chamber_positive_of_isProP hD hcomp E hE _ ((hpos C).conjugate g) (by
      rw [hfix]
      exact Subgroup.map_mono (facetPositiveSubgroup_le_facetZeroFixer D C hD))
  have hfixinv : conjugateSubgroup g⁻¹ (facetZeroFixer D E) = facetZeroFixer D C := by
    rw [hfix, ← conjugateSubgroup_mul, inv_mul_cancel, conjugateSubgroup_one]
  have hleinv : conjugateSubgroup g⁻¹ (facetPositiveSubgroup D E) ≤
      facetPositiveSubgroup D C :=
    le_chamber_positive_of_isProP hD hcomp C hC _ ((hpos E).conjugate g⁻¹) (by
      rw [← hfixinv]
      exact Subgroup.map_mono (facetPositiveSubgroup_le_facetZeroFixer D E hD))
  apply le_antisymm _ hle
  calc
    facetPositiveSubgroup D E =
        conjugateSubgroup g (conjugateSubgroup g⁻¹ (facetPositiveSubgroup D E)) := by
      rw [← conjugateSubgroup_mul, mul_inv_cancel, conjugateSubgroup_one]
    _ ≤ conjugateSubgroup g (facetPositiveSubgroup D C) := Subgroup.map_mono hleinv

/-- Chamber positive subgroups are conjugate by an element of the zero subgroup. -/
theorem exists_chamber_positive_conjugator
    (hD : D.SatisfiesGroupAxioms) (hcomp : FacetReductiveComparisons D)
    (hpos : ∀ Fa, IsProPSubgroup (ringChar 𝓀[F]) (facetPositiveSubgroup D Fa))
    (C E : BuildingFacet D.base.toValuationBuildingData)
    (hC : D.base.IsChamber C.val) (hE : D.base.IsChamber E.val) :
    ∃ g : D.base.zeroSubgroup, facetPositiveSubgroup D E =
      conjugateSubgroup (g : rationalPoints G) (facetPositiveSubgroup D C) := by
  obtain ⟨g, hg⟩ := exists_chamber_fixer_conjugator hD C E hC hE
  exact ⟨g, chamber_positive_eq_conjugate_of_zeroFixer_eq hD hcomp hpos C E hC hE g hg⟩

/-- Containment between positive subgroups of chambers is equality. -/
theorem eq_chamber_positive_of_le
    (hD : D.SatisfiesGroupAxioms) (hcomp : FacetReductiveComparisons D)
    (hpos : ∀ Fa, IsProPSubgroup (ringChar 𝓀[F]) (facetPositiveSubgroup D Fa))
    (C E : BuildingFacet D.base.toValuationBuildingData)
    (hC : D.base.IsChamber C.val) (hE : D.base.IsChamber E.val)
    (hle : facetPositiveSubgroup D C ≤ facetPositiveSubgroup D E) :
    facetPositiveSubgroup D E = facetPositiveSubgroup D C := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  borelize (rationalPoints G)
  obtain ⟨g, hg⟩ := exists_chamber_positive_conjugator hD hcomp hpos C E hC hE
  rw [hg] at hle ⊢
  exact conjugate_eq_of_le
    (rationalPoints_modularCharacter_eq_one D.base.isConnectedReductive) g _
    (isOpen_facetPositiveSubgroup D C) (isCompact_facetPositiveSubgroup D C) hle

/-- Under the explicit quotient comparisons, finite-field Sylow input and
positive-subgroup pro-p input, every chamber positive subgroup is maximal. -/
theorem isMaximalOpenProPIn_chamber
    (hD : D.SatisfiesGroupAxioms) (hcomp : FacetReductiveComparisons D)
    (hSylow : FiniteFieldSylowBorelStatement.{u})
    (hpos : ∀ Fa, IsProPSubgroup (ringChar 𝓀[F]) (facetPositiveSubgroup D Fa))
    (C : BuildingFacet D.base.toValuationBuildingData) (hC : D.base.IsChamber C.val) :
    IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup
      (facetPositiveSubgroup D C) := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  refine ⟨facetPositiveSubgroup_le_zeroSubgroup D C hD,
    isOpen_facetPositiveSubgroup D C, hpos C, ?_⟩
  intro H hCH hH0 _ hH
  obtain ⟨E, hE, hHE⟩ := exists_chamber_positive_ge_of_isProP hD hcomp hSylow H hH0 hH
  have heq := eq_chamber_positive_of_le hD hcomp hpos C E hC hE (hCH.trans hHE)
  rw [heq] at hHE
  exact le_antisymm hHE hCH

/-- Choose a maximal open pro-p overgroup of a given pro-p subgroup of the zero
subgroup, realized by an actual chamber positive subgroup. -/
def maximalProPSubgroupContaining
    (hD : D.SatisfiesGroupAxioms) (hcomp : FacetReductiveComparisons D)
    (hSylow : FiniteFieldSylowBorelStatement.{u})
    (hpos : ∀ Fa, IsProPSubgroup (ringChar 𝓀[F]) (facetPositiveSubgroup D Fa))
    (H : Subgroup (rationalPoints G)) (hH0 : H ≤ D.base.zeroSubgroup)
    (hH : IsProPSubgroup (ringChar 𝓀[F]) H) :
    {K : Subgroup (rationalPoints G) //
      H ≤ K ∧ IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup K} := by
  let C := proPSubgroupContainingChamber hD hcomp hSylow H hH0 hH
  exact ⟨facetPositiveSubgroup D C.val, C.property.2,
    isMaximalOpenProPIn_chamber hD hcomp hSylow hpos C.val C.property.1⟩

end Langlands.BruhatTits.MaximalProP
