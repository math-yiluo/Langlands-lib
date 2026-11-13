import Langlands.BruhatTits.MaximalProP.AvailableNormalizerQuotient

/-! # Maximal facet positive subgroups force chamberhood in their own fixer -/

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

local instance maximalFacetChamberPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- A maximal facet positive subgroup has torus reductive quotient, by reduction
inside its own fixer. No boundedness assumption on a normalizer is needed. -/
theorem isChamber_of_maximal_facetPositive
    (hD : D.SatisfiesGroupAxioms)
    (hcomp : FacetReductiveComparisons D)
    (hnormal : FiniteFieldNormalSylowTorusStatement.{u})
    (Fa : BuildingFacet D.base.toValuationBuildingData)
    (hpos : IsProPSubgroup (ringChar 𝓀[F]) (facetPositiveSubgroup D Fa))
    (hmax : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup
      (facetPositiveSubgroup D Fa)) :
    D.base.IsChamber Fa.val := by
  have hPF := facetPositiveSubgroup_le_facetZeroFixer D Fa hD
  let P := facetReductionSylow hD Fa (facetPositiveSubgroup D Fa) hmax hPF hpos
  have hFN : facetZeroFixer D Fa ≤
      Subgroup.normalizer (facetPositiveSubgroup D Fa : Set (rationalPoints G)) :=
    (facetZeroFixer_le_facetPositiveZeroNormalizer hD Fa).trans inf_le_left
  have hPN : P.toSubgroup.Normal :=
    normal_facetReductionSylow hD Fa (facetPositiveSubgroup D Fa) hmax hPF hpos hFN
  have hQ := hD.reductiveQuotients.facets.reductive_quotients Fa
  have htorus : IsTorus (D.quotients.quotient Fa).quotient :=
    hnormal 𝓀[F] (D.quotients.quotient Fa).quotient hQ.2.2 P.toSubgroup
      P.isPGroup' (fun K hPK hK => P.is_maximal' hK hPK) hPN
  exact (hcomp.1 Fa).mp htorus

/-- Keep the original maximal-positive facet, certified as a chamber using its
own finite reductive quotient. -/
def maximalPositiveFacetAsChamber
    (hD : D.SatisfiesGroupAxioms)
    (hcomp : FacetReductiveComparisons D)
    (hnormal : FiniteFieldNormalSylowTorusStatement.{u})
    (Fa : BuildingFacet D.base.toValuationBuildingData)
    (hpos : IsProPSubgroup (ringChar 𝓀[F]) (facetPositiveSubgroup D Fa))
    (hmax : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup
      (facetPositiveSubgroup D Fa)) :
    {C : BuildingFacet D.base.toValuationBuildingData // D.base.IsChamber C.val} :=
  ⟨Fa, isChamber_of_maximal_facetPositive hD hcomp hnormal Fa hpos hmax⟩

@[simp] theorem maximalPositiveFacetAsChamber_val
    (hD : D.SatisfiesGroupAxioms)
    (hcomp : FacetReductiveComparisons D)
    (hnormal : FiniteFieldNormalSylowTorusStatement.{u})
    (Fa : BuildingFacet D.base.toValuationBuildingData)
    (hpos : IsProPSubgroup (ringChar 𝓀[F]) (facetPositiveSubgroup D Fa))
    (hmax : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup
      (facetPositiveSubgroup D Fa)) :
    (maximalPositiveFacetAsChamber hD hcomp hnormal Fa hpos hmax).val = Fa := rfl

end Langlands.BruhatTits.MaximalProP
