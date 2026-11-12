import Langlands.Geometry.Building.MetricRealizationStatement
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness

/-! # Fixed points of algebraically bounded subgroups in the actual KP quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

/-- The local-field form of the conclusion of KP Corollary 4.2.14 on supplied data
satisfying the five axioms of the corrected opening of KP Section 4.2.

An algebraically bounded subgroup `H` of `G(F)` (KP Definition 2.2.1) fixes a point of
the existing quotient. Moreover, for every complete NPC metric realization of that
quotient, `H` fixes a point of each nonempty closed geodesically convex subset that it
preserves. The fixed points are chosen before quantifying over the elements of `H`.
No existence of the supplied data, of the axiom witnesses or of a metric realization
is asserted. -/
def BoundedSubgroupFixedPointStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
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
      ∀ H : Subgroup (rationalPoints G),
        IsAlgebraicallyBounded F G.X (H : Set (rationalPoints G)) →
          (∃ x : P.toValuationBuildingData.ReducedBuilding, ∀ h ∈ H, h • x = x) ∧
          ∀ M : P.toValuationBuildingData.MetricRealization,
            letI : MetricSpace P.toValuationBuildingData.ReducedBuilding := M.metric
            ∀ Y : Set P.toValuationBuildingData.ReducedBuilding,
              IsClosed Y →
              Langlands.Geometry.Metric.KP.IsGeodesicallyConvex Y →
              (∀ h ∈ H, ∀ y ∈ Y, h • y ∈ Y) →
              ∃ x ∈ Y, ∀ h ∈ H, h • x = x

end Langlands.Geometry.Building
