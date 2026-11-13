import Langlands.BruhatTits.MaximalProP.AvailablePositiveNormalizer
import Langlands.BruhatTits.MaximalProP.FacetReductiveComparisonStatement
import Langlands.BruhatTits.IntegralModels.DepthZeroProP
import Langlands.Geometry.Building.BuildingChamberIncidence
import Langlands.GroupScheme.Rational.FiniteFieldNormalSylowStatement
import Mathlib.GroupTheory.Sylow

/-! # Reduction of maximal pro-p subgroups and the positive normalizer -/

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

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance : HenselianLocalRing 𝒪[F] := henselianLocalRing_integer

/-- A maximal open pro-p subgroup lying in a facet fixer has Sylow image
under the actual reduction, provided the facet's positive subgroup is pro-p. -/
def facetReductionSylow (hD : D.SatisfiesGroupAxioms)
    (Fa : BuildingFacet D.base.toValuationBuildingData)
    (H : Subgroup (rationalPoints G))
    (hH : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup H)
    (hHF : H ≤ facetZeroFixer D Fa)
    (hpos : IsProPSubgroup (ringChar 𝓀[F]) (facetPositiveSubgroup D Fa)) :
    Sylow (ringChar 𝓀[F]) (rationalPoints (D.quotients.quotient Fa).quotient) := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  let Q := D.quotients.quotient Fa
  let I := (D.models.facetModels.model Fa).neutral.integralPoints
  have hIF : I = facetZeroFixer D Fa :=
    hD.bruhatTitsGroupSchemes.neutral_points (BuildingModelIndex.ofFacet Fa)
  have hHI : H ≤ I := hIF ▸ hHF
  have hI0 : I ≤ D.base.zeroSubgroup := hIF ▸ inf_le_right
  have hQ := hD.reductiveQuotients.facets.reductive_quotients Fa
  refine
    { toSubgroup := (H.subgroupOf I).map Q.parahoricReduction
      isPGroup' := Q.localField_isPGroup_reductionImage hH.2.2.1 hHI
      is_maximal' := ?_ }
  intro P hP hSP
  let L := Q.localFieldReductionPreimage P
  have hHL : H ≤ L.toSubgroup := by
    intro g hg
    refine ⟨⟨g, hHI hg⟩, hSP ?_, rfl⟩
    exact ⟨⟨g, hHI hg⟩, hg, rfl⟩
  have hL0 : L.toSubgroup ≤ D.base.zeroSubgroup :=
    (Q.localFieldReductionPreimage_le_integralPoints P).trans hI0
  have hLP : IsProPSubgroup (ringChar 𝓀[F]) L.toSubgroup :=
    Q.localField_isProP_reductionPreimage hQ.2.1 hpos P hP
  have hLH : L.toSubgroup = H := hH.2.2.2 L.toSubgroup hHL hL0 L.isOpen hLP
  have hcomap : P.comap Q.parahoricReduction = H.subgroupOf I := by
    rw [← Q.localFieldReductionPreimage_subgroupOf P]
    exact congrArg (fun K : Subgroup (rationalPoints G) => K.subgroupOf I) hLH
  calc
    P = (P.comap Q.parahoricReduction).map Q.parahoricReduction :=
      (Subgroup.map_comap_eq_self_of_surjective
        (Q.parahoricReduction_surjective hQ.1 hQ.2.1) P).symm
    _ = (H.subgroupOf I).map Q.parahoricReduction :=
      congrArg (Subgroup.map Q.parahoricReduction) hcomap

@[simp]
theorem facetReductionSylow_toSubgroup (hD : D.SatisfiesGroupAxioms)
    (Fa : BuildingFacet D.base.toValuationBuildingData)
    (H : Subgroup (rationalPoints G))
    (hH : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup H)
    (hHF : H ≤ facetZeroFixer D Fa)
    (hpos : IsProPSubgroup (ringChar 𝓀[F]) (facetPositiveSubgroup D Fa)) :
    (facetReductionSylow hD Fa H hH hHF hpos).toSubgroup =
      (H.subgroupOf (D.models.facetModels.model Fa).neutral.integralPoints).map
        (D.quotients.quotient Fa).parahoricReduction := rfl

/-- When the facet fixer normalizes the maximal subgroup, its Sylow image
under actual parahoric reduction is normal in the whole quotient point group. -/
theorem normal_facetReductionSylow (hD : D.SatisfiesGroupAxioms)
    (Fa : BuildingFacet D.base.toValuationBuildingData)
    (H : Subgroup (rationalPoints G))
    (hH : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup H)
    (hHF : H ≤ facetZeroFixer D Fa)
    (hpos : IsProPSubgroup (ringChar 𝓀[F]) (facetPositiveSubgroup D Fa))
    (hFN : facetZeroFixer D Fa ≤ Subgroup.normalizer (H : Set (rationalPoints G))) :
    (facetReductionSylow hD Fa H hH hHF hpos).toSubgroup.Normal := by
  rw [facetReductionSylow_toSubgroup]
  let I := (D.models.facetModels.model Fa).neutral.integralPoints
  have hIF : I = facetZeroFixer D Fa :=
    hD.bruhatTitsGroupSchemes.neutral_points (BuildingModelIndex.ofFacet Fa)
  have hHI : H ≤ I := hIF ▸ hHF
  have hn : (H.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHI).mpr (hIF ▸ hFN)
  have hQ := hD.reductiveQuotients.facets.reductive_quotients Fa
  exact hn.map _ ((D.quotients.quotient Fa).parahoricReduction_surjective hQ.1 hQ.2.1)

/-- Explicit finite and boundedness inputs turn maximality of a facet positive
subgroup into chamberhood and identify its positive normalizer with its fixer. -/
theorem isChamber_and_normalizer_eq_of_maximal
    (hD : D.SatisfiesGroupAxioms)
    (hcomp : FacetReductiveComparisons D)
    (hnormal : FiniteFieldNormalSylowTorusStatement.{u})
    (hpos : ∀ Fa : BuildingFacet D.base.toValuationBuildingData,
      IsProPSubgroup (ringChar 𝓀[F]) (facetPositiveSubgroup D Fa))
    (C : BuildingFacet D.base.toValuationBuildingData)
    (hmax : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup
      (facetPositiveSubgroup D C))
    (hb : IsAlgebraicallyBounded F G.X
      ((Subgroup.normalizer (facetPositiveSubgroup D C : Set (rationalPoints G)) ⊓
        Langlands.Plancherel.rationalCommonNormKernel G) : Set (rationalPoints G))) :
    D.base.IsChamber C.val ∧
      facetPositiveZeroNormalizer D C = facetZeroFixer D C := by
  let N := positiveNormalizerFacet hD C hb
  have hHN : facetPositiveSubgroup D C ≤ facetZeroFixer D N.val := by
    rw [← N.property.1]
    exact (facetPositiveSubgroup_le_facetZeroFixer D C hD).trans
      (facetZeroFixer_le_facetPositiveZeroNormalizer hD C)
  have hNF : facetZeroFixer D N.val ≤
      Subgroup.normalizer (facetPositiveSubgroup D C : Set (rationalPoints G)) := by
    rw [← N.property.1]
    exact inf_le_left
  let P := facetReductionSylow hD N.val (facetPositiveSubgroup D C) hmax hHN (hpos N.val)
  have hPN : P.toSubgroup.Normal :=
    normal_facetReductionSylow hD N.val (facetPositiveSubgroup D C) hmax hHN
      (hpos N.val) hNF
  have hQ := hD.reductiveQuotients.facets.reductive_quotients N.val
  have htorus : IsTorus (D.quotients.quotient N.val).quotient :=
    hnormal 𝓀[F] (D.quotients.quotient N.val).quotient hQ.2.2 P.toSubgroup
      P.isPGroup' (fun K hPK hK => P.is_maximal' hK hPK) hPN
  have hNC : D.base.IsChamber N.val.val := (hcomp.1 N.val).mp htorus
  have heq : N.val = C :=
    D.base.toValuationBuildingData.eq_of_isChamber_of_facetPrecedes
      hD.affineRootSystem.apartmentAxioms hNC N.property.2
  exact ⟨heq ▸ hNC, N.property.1.trans (congrArg (facetZeroFixer D) heq)⟩

end Langlands.BruhatTits.MaximalProP
