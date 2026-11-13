import Langlands.BruhatTits.MaximalProP.AvailableNormalizerQuotient
import Langlands.BruhatTits.IntegralModels.PositiveProPStatement
import Langlands.BruhatTits.RationalPoints.BoundedOpenNormalizerStatement

/-! # Applying the local-model and normalizer inputs to actual facets -/

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

/-- The explicit smooth-model pro-p input applies to each actual facet model. -/
theorem isProP_facetPositiveSubgroup (hD : D.SatisfiesGroupAxioms)
    (hpositive : LocalFieldPositiveProPStatement.{u})
    (Fa : BuildingFacet D.base.toValuationBuildingData) :
    IsProPSubgroup (ringChar 𝓀[F]) (facetPositiveSubgroup D Fa) := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  exact hpositive F G (D.models.facetModels.model Fa) (D.quotients.quotient Fa)
    (hD.reductiveQuotients.facets.reductive_quotients Fa)

/-- Compactness and openness of the actual radical preimage supply the hypotheses
of the explicit bounded-open-normalizer input. -/
theorem isAlgebraicallyBounded_facetPositiveNormalizer
    (hbounded : RationalPoints.BoundedOpenNormalizerStatement.{u})
    (Fa : BuildingFacet D.base.toValuationBuildingData) :
    IsAlgebraicallyBounded F G.X
      ((Subgroup.normalizer (facetPositiveSubgroup D Fa : Set (rationalPoints G)) ⊓
        Langlands.Plancherel.rationalCommonNormKernel G) : Set (rationalPoints G)) := by
  let : Smooth G.X.hom := D.base.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have hopen := isOpen_facetPositiveSubgroup D Fa
  have hclosed := Subgroup.isClosed_of_isOpen (facetPositiveSubgroup D Fa) hopen
  have hbound := (localFieldAffineBoundedCompactness_proof F G.X _ hclosed).mpr
    (isCompact_facetPositiveSubgroup D Fa)
  exact hbounded F G D.base.isConnectedReductive (facetPositiveSubgroup D Fa) hbound hopen

/-- Specialize the conditional normalizer argument using the actual local models
and the explicit local-model and bounded-normalizer theorem inputs. -/
theorem isChamber_and_normalizer_eq_of_maximal_from_inputs
    (hD : D.SatisfiesGroupAxioms)
    (hcomp : FacetReductiveComparisons D)
    (hnormal : FiniteFieldNormalSylowTorusStatement.{u})
    (hpositive : LocalFieldPositiveProPStatement.{u})
    (hbounded : RationalPoints.BoundedOpenNormalizerStatement.{u})
    (Fa : BuildingFacet D.base.toValuationBuildingData)
    (hmax : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup
      (facetPositiveSubgroup D Fa)) :
    D.base.IsChamber Fa.val ∧
      facetPositiveZeroNormalizer D Fa = facetZeroFixer D Fa :=
  isChamber_and_normalizer_eq_of_maximal hD hcomp hnormal
    (isProP_facetPositiveSubgroup hD hpositive) Fa hmax
    (isAlgebraicallyBounded_facetPositiveNormalizer hbounded Fa)

/-- Refine the given maximal-positive facet to a chamber with its normalizer
identity, retaining the same underlying facet. All theorem inputs are explicit. -/
def maximalFacetPositiveChamber
    (hD : D.SatisfiesGroupAxioms)
    (hcomp : FacetReductiveComparisons D)
    (hnormal : FiniteFieldNormalSylowTorusStatement.{u})
    (hpositive : LocalFieldPositiveProPStatement.{u})
    (hbounded : RationalPoints.BoundedOpenNormalizerStatement.{u})
    (Fa : BuildingFacet D.base.toValuationBuildingData)
    (hmax : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup
      (facetPositiveSubgroup D Fa)) :
    {C : BuildingFacet D.base.toValuationBuildingData //
      D.base.IsChamber C.val ∧
        facetPositiveZeroNormalizer D C = facetZeroFixer D C} :=
  ⟨Fa, isChamber_and_normalizer_eq_of_maximal_from_inputs
    hD hcomp hnormal hpositive hbounded Fa hmax⟩

@[simp]
theorem maximalFacetPositiveChamber_val
    (hD : D.SatisfiesGroupAxioms)
    (hcomp : FacetReductiveComparisons D)
    (hnormal : FiniteFieldNormalSylowTorusStatement.{u})
    (hpositive : LocalFieldPositiveProPStatement.{u})
    (hbounded : RationalPoints.BoundedOpenNormalizerStatement.{u})
    (Fa : BuildingFacet D.base.toValuationBuildingData)
    (hmax : IsMaximalOpenProPIn (ringChar 𝓀[F]) D.base.zeroSubgroup
      (facetPositiveSubgroup D Fa)) :
    (maximalFacetPositiveChamber hD hcomp hnormal hpositive hbounded Fa hmax).val = Fa :=
  rfl

end Langlands.BruhatTits.MaximalProP
