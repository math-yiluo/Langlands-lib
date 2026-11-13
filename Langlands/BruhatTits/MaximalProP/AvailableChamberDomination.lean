import Langlands.BruhatTits.MaximalProP.AvailableFixedFacet
import Langlands.BruhatTits.MaximalProP.FacetReductiveComparisonStatement
import Langlands.BruhatTits.IntegralModels.DepthZeroProP
import Langlands.GroupScheme.Rational.FiniteFieldSylowBorelStatement
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport
import Mathlib.GroupTheory.Sylow

/-! # Chamber radical preimages containing pro-p subgroups -/

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

local instance chamberDominationAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance chamberDominationPointTopology : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

set_option maxHeartbeats 1000000 in
/-- A pro-p subgroup in a facet fixer lies in the positive subgroup of an
incident chamber, under the finite-field and facet comparison inputs. -/
theorem exists_incident_chamber_of_isProP
    (hD : D.SatisfiesGroupAxioms) (hcomp : FacetReductiveComparisons D)
    (hSylow : FiniteFieldSylowBorelStatement.{u})
    (Fa : BuildingFacet D.base.toValuationBuildingData)
    (H : Subgroup (rationalPoints G)) (hH : IsProPSubgroup (ringChar 𝓀[F]) H)
    (hHF : H ≤ facetZeroFixer D Fa) :
    ∃ C : IncidentFacets D.base.toValuationBuildingData Fa,
      D.base.IsChamber C.val.val ∧ H ≤ facetPositiveSubgroup D C.val := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  let Q := D.quotients.quotient Fa
  let I := (D.models.facetModels.model Fa).neutral.integralPoints
  have hHI : H ≤ I := by
    change H ≤ (D.models.model (BuildingModelIndex.ofFacet Fa)).neutral.integralPoints
    rw [hD.bruhatTitsGroupSchemes.neutral_points]
    exact hHF
  have hp := Q.localField_isPGroup_reductionImage hH hHI
  obtain ⟨P, hHP⟩ := hp.exists_le_sylow
  obtain ⟨B, U, i, j, hi, hj, hP⟩ :=
    (hSylow 𝓀[F] Q.quotient
      (hD.reductiveQuotients.facets.reductive_quotients Fa).2.2
      P.toSubgroup).mp
      ⟨P.isPGroup', fun P' hle hp' => P.is_maximal' hp' hle⟩
  obtain ⟨C, hC⟩ := (hD.reductiveQuotients.facets.parabolic_order Fa).surjective
    (SubgroupFunctor.range i) ⟨B, i, hi.isParabolicSubgroup, rfl⟩
  let φ := D.models.facetModels.morphism Fa C.val C.property
  let i' := φ.reductiveImageInclusion Q
  have hci : SubgroupFunctor.range i' = SubgroupFunctor.range i := hC
  have : IsClosedImmersion i.hom.hom.left := hi.1.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  let hr : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let hr' : (SubgroupFunctor.range i).IsRepresentedBy i' :=
    ⟨inferInstance, hci⟩
  let e : B ≅ φ.reductiveImage Q := hr.isoOfIsRepresentedBy hr'
  have he : e.hom ≫ i' = i := hr.isoOfIsRepresentedBy_hom_comp hr'
  have he' : e.inv ≫ i = i' := by rw [← he, Iso.inv_hom_id_assoc]
  have hi' : IsGeometricBorelSubgroup i' := by
    rw [← he']
    refine ⟨hi.1.iso_comp e.symm, ?_⟩
    let bc := GroupScheme.baseChange (toAlgebraicClosure 𝓀[F])
    change IsBorelSubgroup (bc.map (e.inv ≫ i))
    rw [bc.map_comp]
    exact hi.2.iso_comp (bc.mapIso e.symm)
  have hch : D.base.IsChamber C.val.val := (hcomp.2.1 Fa C.val C.property).mp hi'
  have hlift := hcomp.2.2 Fa C.val C.property U (j ≫ e.hom) (hj.comp_iso e)
  have hrad : (j ≫ e.hom) ≫ i' = j ≫ i := by rw [Category.assoc, he]
  change (((rationalPoints.map ((j ≫ e.hom) ≫ i')).range.comap
    Q.parahoricReduction).map I.subtype) = facetPositiveSubgroup D C.val at hlift
  rw [hrad, ← hP] at hlift
  refine ⟨C, hch, ?_⟩
  rw [← hlift]
  intro g hg
  refine ⟨⟨g, hHI hg⟩, ?_, rfl⟩
  exact hHP ⟨⟨g, hHI hg⟩, hg, rfl⟩

/-- Every pro-p subgroup of the zero subgroup lies in a chamber radical
preimage, under the explicit finite-field and facet comparison inputs. -/
theorem exists_chamber_positive_ge_of_isProP
    (hD : D.SatisfiesGroupAxioms) (hcomp : FacetReductiveComparisons D)
    (hSylow : FiniteFieldSylowBorelStatement.{u})
    (H : Subgroup (rationalPoints G)) (hH0 : H ≤ D.base.zeroSubgroup)
    (hH : IsProPSubgroup (ringChar 𝓀[F]) H) :
    ∃ C : BuildingFacet D.base.toValuationBuildingData,
      D.base.IsChamber C.val ∧ H ≤ facetPositiveSubgroup D C := by
  obtain ⟨Fa, hHF⟩ := exists_le_facetZeroFixer_of_isProP hD H hH0 hH
  obtain ⟨C, hC, hHC⟩ := exists_incident_chamber_of_isProP hD hcomp hSylow Fa H hH hHF
  exact ⟨C.val, hC, hHC⟩

/-- Choose a chamber whose actual radical preimage contains the supplied
pro-p subgroup of the zero subgroup. -/
def proPSubgroupContainingChamber
    (hD : D.SatisfiesGroupAxioms) (hcomp : FacetReductiveComparisons D)
    (hSylow : FiniteFieldSylowBorelStatement.{u})
    (H : Subgroup (rationalPoints G)) (hH0 : H ≤ D.base.zeroSubgroup)
    (hH : IsProPSubgroup (ringChar 𝓀[F]) H) :
    { C : BuildingFacet D.base.toValuationBuildingData //
      D.base.IsChamber C.val ∧ H ≤ facetPositiveSubgroup D C } :=
  ⟨Classical.choose (exists_chamber_positive_ge_of_isProP hD hcomp hSylow H hH0 hH),
    Classical.choose_spec (exists_chamber_positive_ge_of_isProP hD hcomp hSylow H hH0 hH)⟩

end Langlands.BruhatTits.MaximalProP
