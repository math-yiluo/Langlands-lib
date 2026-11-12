import Langlands.Geometry.Building.ValuationBuildingCompleteness

/-! # Unions of closed facets of the actual KP quotient are closed -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

open ValuationBuildingData

attribute [local instance] metricRootFintype RootTranslationMetric.normedAddCommGroup
  RootTranslationMetric.normedSpace apartmentMetricSpace apartmentNormedAddTorsor

/-- The second assertion of KP Theorem 4.2.10 for the existing quotient of supplied
valuation building data. The metric on `B(G)` is any metric for which `G(F)` acts by
isometries and the apartment map `A(S) → B(G)` is an isometry for the Euclidean root
metric of `ValuationApartmentMetric`, under the same hypotheses as the published
completeness theorem: any two points share an apartment, and `SatisfiesApartmentAxioms`
holds, i.e. V 6, V 7 and AS 2–AS 5 (V 6 is part of the data `B`; V 7, compatibility of the
root filtrations with the topology of `G(F)`, is an additional premise).
For every set `X` of facets of `B(G)`, the union of their topological closures is
closed. No existence of the data, of the metric or of the hypotheses is asserted. -/
def FacetClosureUnionClosedStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)
    [MetricSpace B.ReducedBuilding] [IsIsometricSMul (rationalPoints G) B.ReducedBuilding],
    (∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x) →
    B.SatisfiesApartmentAxioms →
    Isometry B.apartmentMap →
    ∀ X : Set (Set B.ReducedBuilding), (∀ Y ∈ X, B.IsFacet Y) →
      IsClosed (⋃ Y ∈ X, closure Y)

end Langlands.Geometry.Building
