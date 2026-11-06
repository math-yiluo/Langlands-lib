import Langlands.Geometry.Building.MetricRealizationStatement
import Langlands.Geometry.Building.CommonApartmentConstruction
import Langlands.Geometry.Building.ValuationBuildingCompleteness
import Langlands.Geometry.Building.ValuationBuildingOrbitContinuity
import Langlands.Geometry.Metric.RetractionGluing

/-! # Assembling a metric realization from apartment retractions

KP Section 4.2 for the existing quotient `B(G)`: a `G(F)`-invariant function
`d` on `B(G)` which restricts to the Euclidean root metric on `A(S)` and admits,
for every point `a` of `A(S)`, a `d`-nonincreasing retraction onto `A(S)`
preserving the distance from `a`, is a complete nonpositively curved metric
(KP Propositions 4.2.3(1), 4.2.7 and Theorem 4.2.10). Together with the
orbit continuity of the bounded-open-stabilizer axiom this is a
`MetricRealization`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

private instance metricAssemblyAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance metricAssemblyGroupTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

attribute [local instance] metricRootFintype RootTranslationMetric.normedAddCommGroup
  RootTranslationMetric.normedSpace apartmentMetricSpace apartmentNormedAddTorsor

/-- A candidate building distance `d` on `B(G)` with the properties KP Section
4.2 establishes for its distance: `d` is `G(F)`-invariant, restricts along the
apartment map to the Euclidean root metric of `A(S)`, and for every point `a`
of `A(S)` there is a retraction `ρ : B(G) → A(S)` fixing `A(S)`, not increasing
distances, and preserving the distance from `a` (KP Proposition 4.2.2 and
the retractions of KP Proposition 4.2.3). -/
structure IsRetractionBuildingDistance (d : B.ReducedBuilding → B.ReducedBuilding → ℝ) :
    Prop where
  /-- `d` is invariant under the existing action of `G(F)`. -/
  smul : ∀ (g : rationalPoints G) (x y : B.ReducedBuilding), d (g • x) (g • y) = d x y
  /-- `d` restricts to the Euclidean root metric on `A(S)`. -/
  apartmentMap : ∀ a b : B.Apartment, d (B.apartmentMap a) (B.apartmentMap b) = dist a b
  /-- Retractions onto `A(S)` centred at each of its points. -/
  exists_retraction : ∀ a : B.Apartment, ∃ ρ : B.ReducedBuilding → B.Apartment,
    (∀ b : B.Apartment, ρ (B.apartmentMap b) = b) ∧
      (∀ x y : B.ReducedBuilding, dist (ρ x) (ρ y) ≤ d x y) ∧
      ∀ x : B.ReducedBuilding, dist a (ρ x) = d (B.apartmentMap a) x

namespace IsRetractionBuildingDistance

variable {B} {d : B.ReducedBuilding → B.ReducedBuilding → ℝ}
  (hd : B.IsRetractionBuildingDistance d)
include hd

/-- On a translated apartment `g • A(S)`, the distance `d` is the Euclidean
root metric transported by `g`. -/
theorem smul_apartmentMap (g : rationalPoints G) (a b : B.Apartment) :
    d (g • B.apartmentMap a) (g • B.apartmentMap b) = dist a b := by
  rw [hd.smul, hd.apartmentMap]

/-- The translated apartment chart is injective. -/
theorem injective_smul_apartmentMap (g : rationalPoints G) :
    Function.Injective (fun a : B.Apartment => g • B.apartmentMap a) := by
  intro a b hab
  apply dist_eq_zero.mp
  rw [← hd.smul_apartmentMap g a b]
  rw [show g • B.apartmentMap b = g • B.apartmentMap a from hab.symm,
    hd.smul_apartmentMap, dist_self]

/-- The translated apartments `g • A(S)`, with the retractions transported from
`A(S)`, satisfy the gluing hypotheses of KP Propositions 4.2.3(1) and 4.2.7. -/
theorem isRetractionGluedDistance (hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x) :
    Metric.KP.IsRetractionGluedDistance d {Y | B.IsApartment Y} where
  exists_common x y := hcommon x y
  apartment := by
    rintro _ ⟨g, rfl⟩
    rw [apartmentImage, Set.smul_set_range]
    exact Metric.KP.exists_apartmentMetric_of_injective B.apartment_nonpositivelyCurved d
      (fun a => g • B.apartmentMap a) (hd.injective_smul_apartmentMap g)
      (hd.smul_apartmentMap g)
  exists_retraction := by
    rintro _ ⟨g, rfl⟩ m hm
    obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hm
    obtain ⟨ρ, hρid, hρle, hρa⟩ := hd.exists_retraction a
    refine ⟨fun x => g • B.apartmentMap (ρ (g⁻¹ • x)), fun x => ?_, ?_, fun x y => ?_,
      fun x => ?_⟩
    · exact Set.smul_mem_smul_set (Set.mem_range_self _)
    · intro x hx
      obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hx
      simp only [inv_smul_smul, hρid]
    · rw [hd.smul_apartmentMap, ← hd.smul g⁻¹ x y]
      exact hρle _ _
    · rw [hd.smul_apartmentMap, hρa, ← hd.smul g, smul_inv_smul]

end IsRetractionBuildingDistance

variable {B}

/-- KP Section 4.2 for the existing quotient: a building distance with the
properties of `IsRetractionBuildingDistance` is a complete nonpositively curved
metric on `B(G)` for which `G(F)` acts isometrically, given common apartments,
AS 2–AS 5, and open stabilizers for the continuity of orbits. -/
theorem nonempty_metricRealization_of_isRetractionBuildingDistance
    (hB : B.HasBoundedOpenStabilizers)
    (hcommon : ∀ x : B.ReducedBuilding, B.HasCommonApartmentWith x)
    (hD : B.SatisfiesApartmentAxioms)
    {d : B.ReducedBuilding → B.ReducedBuilding → ℝ} (hd : B.IsRetractionBuildingDistance d) :
    Nonempty B.MetricRealization := by
  have hglue := hd.isRetractionGluedDistance hcommon
  let := hglue.metricSpace
  have : IsIsometricSMul (rationalPoints G) B.ReducedBuilding :=
    ⟨fun g => Isometry.of_dist_eq (hd.smul g)⟩
  have : CompleteSpace B.ReducedBuilding :=
    completeSpace_of_isometry_apartmentMap_of_satisfiesApartmentAxioms hcommon hD
      (Isometry.of_dist_eq hd.apartmentMap)
  exact ⟨{ nonpositivelyCurved := hglue.isNonpositivelyCurved
           continuous_orbit := B.continuous_orbit_of_hasBoundedOpenStabilizers hB }⟩

/-- The metric-realization statement follows once every supplied datum satisfying
the hypotheses of `MetricRealizationStatement` carries a building distance with
the properties of `IsRetractionBuildingDistance`. -/
theorem metricRealizationStatement_of_exists_isRetractionBuildingDistance
    (h : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
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
        ∃ d, P.toValuationBuildingData.IsRetractionBuildingDistance d) :
    MetricRealizationStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro P R T hR hB hT hRR hD hC hTits
  obtain ⟨d, hd⟩ := h F G hG P R T hR hB hT hRR hD hC hTits
  exact nonempty_metricRealization_of_isRetractionBuildingDistance hB
    (R.hasCommonApartmentWith_of_isBuilding hR.isBuilding) hD hd

end Langlands.Geometry.Building.ValuationBuildingData
