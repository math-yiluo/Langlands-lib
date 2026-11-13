import Langlands.BruhatTits.MaximalProP.AvailableChamberMaximality
import Langlands.BruhatTits.MaximalProP.AvailableMaximalClassification

/-! # Maximal pro-p conclusions from explicit structural inputs -/

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

local instance conclusionsAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance conclusionsPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- Assemble all four corrected KP conclusions while retaining the five
structural inputs explicitly. -/
theorem maximalProPConclusions_of_inputs
    (hD : D.SatisfiesGroupAxioms) (hcomp : FacetReductiveComparisons D)
    (hSylow : FiniteFieldSylowBorelStatement.{u})
    (hnormal : FiniteFieldNormalSylowTorusStatement.{u})
    (hpositive : LocalFieldPositiveProPStatement.{u})
    (hbounded : RationalPoints.BoundedOpenNormalizerStatement.{u}) :
    MaximalProPConclusions D := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  have hpos := isProP_facetPositiveSubgroup hD hpositive
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Fa
    exact ⟨facetPositiveSubgroup_le_zeroSubgroup D Fa hD,
      isOpen_facetPositiveSubgroup D Fa, hpos Fa⟩
  · intro Fa
    exact ⟨fun hmax => (isChamber_and_normalizer_eq_of_maximal_from_inputs
        hD hcomp hnormal hpositive hbounded Fa hmax).1,
      isMaximalOpenProPIn_chamber hD hcomp hSylow hpos Fa⟩
  · exact exists_chamber_of_isMaximalOpenProP hD hcomp hSylow hpositive
  · intro C hC
    exact (isChamber_and_normalizer_eq_of_maximal_from_inputs
      hD hcomp hnormal hpositive hbounded C
      (isMaximalOpenProPIn_chamber hD hcomp hSylow hpos C hC)).2

/-- The actual chamber-to-positive-subgroup map is a bijection onto the maximal
open pro-p subgroups of the zero subgroup, under the explicit structural inputs. -/
def chamberMaximalOpenProPEquiv
    (hD : D.SatisfiesGroupAxioms) (hcomp : FacetReductiveComparisons D)
    (hSylow : FiniteFieldSylowBorelStatement.{u})
    (hnormal : FiniteFieldNormalSylowTorusStatement.{u})
    (hpositive : LocalFieldPositiveProPStatement.{u})
    (hbounded : RationalPoints.BoundedOpenNormalizerStatement.{u}) :
    {C : BuildingFacet D.base.toValuationBuildingData // D.base.IsChamber C.val} ≃
      {H : Subgroup (rationalPoints G) //
        IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup H} := by
  let f : {C : BuildingFacet D.base.toValuationBuildingData // D.base.IsChamber C.val} →
      {H : Subgroup (rationalPoints G) //
        IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup H} :=
    fun C => ⟨facetPositiveSubgroup D C.val,
      isMaximalOpenProPIn_chamber hD hcomp hSylow
        (isProP_facetPositiveSubgroup hD hpositive) C.val C.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro C E heq
    apply Subtype.ext
    exact eq_of_facetPositiveSubgroup_eq_of_isMaximalOpenProP
      hD hcomp hnormal hpositive hbounded C.val E.val (f C).property
      (congrArg Subtype.val heq)
  · rintro ⟨H, hH⟩
    obtain ⟨C, hC, hHC⟩ := exists_chamber_of_isMaximalOpenProP
      hD hcomp hSylow hpositive H hH
    refine ⟨⟨C, hC⟩, ?_⟩
    apply Subtype.ext
    exact hHC.symm

end Datum

/-- The five explicit structural propositions imply the availability-only target.
This implication does not assert the five propositions. -/
theorem availableMaximalProP_of_inputs
    (hcomp : FacetReductiveComparisonStatement.{u})
    (hSylow : FiniteFieldSylowBorelStatement.{u})
    (hnormal : FiniteFieldNormalSylowTorusStatement.{u})
    (hpositive : LocalFieldPositiveProPStatement.{u})
    (hbounded : RationalPoints.BoundedOpenNormalizerStatement.{u}) :
    AvailableMaximalProPStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro 𝔅 h𝔅
  exact maximalProPConclusions_of_inputs h𝔅.groupAxioms
    (hcomp F G (𝔅.datum F G hG) h𝔅.groupAxioms) hSylow hnormal hpositive hbounded

end Langlands.BruhatTits.MaximalProP
