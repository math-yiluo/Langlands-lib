import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Metric.KPDefinitions
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups

/-! # The metric construction on the actual KP quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

private instance metricRealizationAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance metricRealizationGroupTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- A complete NPC metric on this same root-valuation quotient, for which its
existing rational-point action is isometric and has continuous orbit maps in
exactly the canonical rational-point topology. No metric normalization is fixed.
Existence of such a realization is not part of `ValuationBuildingData`. -/
structure MetricRealization where
  [metric : MetricSpace B.ReducedBuilding]
  [complete : CompleteSpace B.ReducedBuilding]
  nonpositivelyCurved :
    Langlands.Geometry.Metric.KP.IsNonpositivelyCurved B.ReducedBuilding
  [isometric : IsIsometricSMul (rationalPoints G) B.ReducedBuilding]
  continuous_orbit : ∀ x : B.ReducedBuilding,
    Continuous (fun g : rationalPoints G => g • x)

end ValuationBuildingData

/-- The metric-construction consequence of KP Section 4.2, under the five
axioms in its corrected opening: 4.1.1, 4.1.2, 4.1.4, 4.1.6 and 4.1.9.

The source's affine-root-system axiom is written as its three existing
Library predicates. All geometric hypotheses concern the same supplied data.
This statement neither assumes a metric nor asserts existence of the supplied
building, splitting, realization or axiom witnesses. -/
def MetricRealizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (P : ParahoricBuildingData G)
      (R : P.toValuationBuildingData.PolysimplicialRealization)
      (T : P.toValuationBuildingData.ApartmentSplitting),
      P.SatisfiesBuildingAxiom R →
      P.HasBoundedOpenStabilizers →
      P.SatisfiesAffineApartmentAxiom T →
      P.HasRootReflections →
      P.SatisfiesApartmentAxioms →
      P.HasCompatibleApartmentFacets →
      P.HasTitsSystem →
      Nonempty P.toValuationBuildingData.MetricRealization

end Langlands.Geometry.Building
