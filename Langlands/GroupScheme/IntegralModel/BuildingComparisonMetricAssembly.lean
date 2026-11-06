import Langlands.GroupScheme.IntegralModel.BuildingComparisonAssembly
import Langlands.Geometry.Building.MetricRealizationProof

/-! # Construct the comparison metric from the five geometric axioms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.BruhatTits.IntegralModels

namespace Langlands.GroupScheme.IntegralModel.BuildingComparison

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
    (hE : RelativeRoot.HasOppositeFactorPairs P.i)
    (x : P.Apartment)
    (hx : AffineRootSystem.IsSpecialPoint P.affineRoots x)

/-- Construct a comparison for the original supplied model using the published
metric construction on the same quotient. The five geometric axioms, opposite
pairs, special point and exact original-model image equality remain inputs. -/
def ofParahoricApartmentSpecialPoint
    (hM : M.integralPoints = P.compactStabilizer (P.apartmentMap x)) :
    BuildingComparison M :=
  ofApartmentSpecialPoint M P.toValuationBuildingData
    (Classical.choice
      (metricRealization F G P.isConnectedReductive P R T hR hB hT hRR hA hC hTits))
    R hR.isBuilding hA hE hC.injective x hx hM

@[simp] theorem ofParahoricApartmentSpecialPoint_building
    (hM : M.integralPoints = P.compactStabilizer (P.apartmentMap x)) :
    (ofParahoricApartmentSpecialPoint M P R T hR hB hT hRR hA hC hTits hE x hx hM).building =
      P.toValuationBuildingData :=
  rfl

@[simp] theorem ofParahoricApartmentSpecialPoint_point
    (hM : M.integralPoints = P.compactStabilizer (P.apartmentMap x)) :
    (ofParahoricApartmentSpecialPoint M P R T hR hB hT hRR hA hC hTits hE x hx hM).point =
      P.apartmentMap x :=
  rfl

/-- Identify the original supplied model with the full singleton-facet model by
an identity-generic model isomorphism, then construct its comparison metric from
the same five geometric axioms. -/
def ofParahoricApartmentFamilyModelIso
    (family : BuildingModelFamily P.toValuationBuildingData ↥𝒪[F])
    (hpoints : ∀ Ω, (family.model Ω).full.integralPoints =
      BuildingModelFamily.oneFixer Ω)
    (e : M.Iso
      (family.model (P.vertexModelIndex (P.apartmentMap x)
        (P.isVertex_apartmentMap
          (AffineRootSystem.isVertex_of_isSpecialPoint
            hA.isAffineRootSystem_affineRoots hx)))).full
      (CategoryTheory.Iso.refl G)) :
    BuildingComparison M :=
  ofParahoricApartmentSpecialPoint M P R T hR hB hT hRR hA hC hTits hE x hx
    (e.integralPoints_eq.trans
      (P.integralPoints_vertexModelIndex family hpoints _ _))

end Langlands.GroupScheme.IntegralModel.BuildingComparison
