import Langlands.GroupScheme.IntegralModel.BuildingComparisonMetricAssembly
import Langlands.Geometry.Building.RootValuationBuildingConstructionStatement
import Langlands.Geometry.Building.SpecialPointGlobalFixedLocus
import Langlands.Geometry.Building.ChamberIwahoriProof

/-! # The supplied-model special-stabilizer identity and the comparison reduction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.GroupScheme.IntegralModel

namespace BuildingComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (M : IntegralModel ↥𝒪[F] F G)
    (P : ParahoricBuildingData G)
    (R : P.toValuationBuildingData.PolysimplicialRealization)
    (T : P.toValuationBuildingData.ApartmentSplitting)
    (hR : P.SatisfiesBuildingAxiom R)
    (hB : P.HasBoundedOpenStabilizers)
    (hT : P.SatisfiesAffineApartmentAxiom T)
    (hRR : P.HasRootReflections)
    (hA : P.SatisfiesApartmentAxioms)
    (hC : P.HasCompatibleApartmentFacets)
    (hTits : P.HasTitsSystem)

/-- Construct a comparison for the original supplied model at an arbitrary
special point of the existing quotient, not necessarily in the image of the
standard apartment. The metric is the published construction from the seven
axiom predicates; vertexhood is translated from the apartment, and uniqueness
is the published global fixed-locus theorem for special building points. -/
def ofParahoricSpecialPoint (y : P.ReducedBuilding) (hy : P.IsSpecialPoint y)
    (hM : M.integralPoints = P.compactStabilizer y) :
    BuildingComparison M :=
  let metric : P.toValuationBuildingData.MetricRealization :=
    Classical.choice
      (metricRealization F G P.isConnectedReductive P R T hR hB hT hRR hA hC hTits)
  letI := metric.metric
  letI := metric.complete
  letI := metric.isometric
  { building := P.toValuationBuildingData
    metric := metric.metric
    complete := metric.complete
    nonpositivelyCurved := metric.nonpositivelyCurved
    isometric := metric.isometric
    continuous_orbit := metric.continuous_orbit
    point := y
    vertex := by
      obtain ⟨g, x, rfl, hx⟩ := hy
      exact ValuationBuildingData.IsVertex.smul _ (P.isVertex_apartmentMap
        (AffineRootSystem.isVertex_of_isSpecialPoint
          hA.isAffineRootSystem_affineRoots hx)) g
    special := hy
    integralPoints_eq := hM
    unique_fixed := by
      intro z hz
      exact P.eq_of_compactStabilizer_fixed_of_special_buildingPoint hA
        P.hasOppositeFactorPairs hC.injective
        (fun x => R.hasCommonApartmentWith_of_isBuilding hR.isBuilding _) hy
        (fun g hg => hz g (hM ▸ hg)) }

@[simp] theorem ofParahoricSpecialPoint_building (y : P.ReducedBuilding)
    (hy : P.IsSpecialPoint y) (hM : M.integralPoints = P.compactStabilizer y) :
    (ofParahoricSpecialPoint M P R T hR hB hT hRR hA hC hTits y hy hM).building =
      P.toValuationBuildingData :=
  rfl

@[simp] theorem ofParahoricSpecialPoint_point (y : P.ReducedBuilding)
    (hy : P.IsSpecialPoint y) (hM : M.integralPoints = P.compactStabilizer y) :
    (ofParahoricSpecialPoint M P R T hR hB hT hRR hA hC hTits y hy hM).point = y :=
  rfl

end BuildingComparison

/-- The supplied-model special-stabilizer identity on every axiom-satisfying
building: for every supplied integral model with connected reductive full special
fibre and every `ParahoricBuildingData` of the generic group satisfying the seven
predicates of `RootValuationBuildingConstructionStatement`, the original model
image is the norm-one stabilizer of a special point of the existing quotient
(Bruhat–Tits II, Proposition 5.1.40 with Proposition 4.6.28(i)). -/
def SpecialStabilizerStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (M : IntegralModel ↥𝒪[F] F G),
    IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group) →
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
      ∃ y : P.ReducedBuilding, P.IsSpecialPoint y ∧
        M.integralPoints = P.compactStabilizer y

/-- The building construction and the supplied-model special-stabilizer identity
together give the exact published comparison target. -/
theorem buildingComparisonStatement_of_specialStabilizer
    (hcon : RootValuationBuildingConstructionStatement.{u})
    (hstab : SpecialStabilizerStatement.{u}) :
    BuildingComparisonStatement.{u} := by
  intro F _ _ _ _ G hG M hspecial
  let _ : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨P, R, T, hR, hB, hT, hRR, hA, hC, hTits⟩ := hcon F G hG
  obtain ⟨y, hy, hM⟩ := hstab F G hG M hspecial P R T hR hB hT hRR hA hC hTits
  exact ⟨BuildingComparison.ofParahoricSpecialPoint M P R T hR hB hT hRR hA hC hTits
    y hy hM⟩

end Langlands.GroupScheme.IntegralModel
