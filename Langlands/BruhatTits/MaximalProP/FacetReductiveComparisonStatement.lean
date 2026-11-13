import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.BruhatTits.IntegralModels.DepthZeroReduction
import Langlands.GroupScheme.Reductive.QuasiSplit

/-! # Facets and the reductive quotients of their supplied KP models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.IntegralModels

namespace Langlands.BruhatTits.MaximalProP

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- Three comparisons on the actual facets, model morphisms and reductive
quotients of one supplied datum. In the last clause the radical preimage is
mapped into the original rational-point group. -/
def FacetReductiveComparisons (D : KPBuildingDatum G) : Prop :=
  (∀ Fa : BuildingFacet D.base.toValuationBuildingData,
    IsTorus (D.quotients.quotient Fa).quotient ↔ D.base.IsChamber Fa.val) ∧
  (∀ (Fa Fb : BuildingFacet D.base.toValuationBuildingData)
    (h : FacetPrecedes D.base.toValuationBuildingData Fa Fb),
    IsGeometricBorelSubgroup
        ((D.models.facetModels.morphism Fa Fb h).reductiveImageInclusion
          (D.quotients.quotient Fa)) ↔
      D.base.IsChamber Fb.val) ∧
  (∀ (Fa Fb : BuildingFacet D.base.toValuationBuildingData)
    (h : FacetPrecedes D.base.toValuationBuildingData Fa Fb),
    let φ := D.models.facetModels.morphism Fa Fb h
    let Q := D.quotients.quotient Fa
    ∀ (U : GroupScheme (Spec (CommRingCat.of 𝓀[F])))
      (j : U ⟶ φ.reductiveImage Q),
      IsUnipotentRadical j →
        (((rationalPoints.map (j ≫ φ.reductiveImageInclusion Q)).range.comap
            Q.parahoricReduction).map
          (D.models.facetModels.model Fa).neutral.integralPoints.subtype) =
        (D.quotients.quotient Fb).positivePoints)

/-- The chamber, Borel and radical-preimage comparisons under the
single-group Bruhat–Tits axioms, over a nonarchimedean local field. -/
def FacetReductiveComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (D : KPBuildingDatum G),
    D.SatisfiesGroupAxioms → FacetReductiveComparisons D

end Langlands.BruhatTits.MaximalProP
