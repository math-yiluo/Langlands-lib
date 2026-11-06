import Langlands.GroupScheme.IntegralModel.BuildingComparison
import Langlands.GroupScheme.IntegralModel.Iso
import Langlands.Geometry.Building.MetricRealizationStatement
import Langlands.Geometry.Building.CommonApartmentConstruction
import Langlands.Geometry.Building.SpecialPointVertices
import Langlands.BruhatTits.IntegralModels.ModelFamily

/-! # Assemble comparisons using the original integral model and one building -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- The singleton of an existing vertex is an actual building facet. -/
theorem isFacet_singleton_of_isVertex {z : B.ReducedBuilding}
    (hz : B.IsVertex z) : B.IsFacet {z} := by
  obtain ⟨g, x, rfl, hx⟩ := hz
  refine ⟨g, {x}, ⟨x, hx⟩, ?_⟩
  exact (Set.image_singleton (f := fun y : B.Apartment => g • B.apartmentMap y)
    (a := x)).symm

/-- The existing family index of the singleton facet at a supplied vertex. -/
def vertexModelIndex (z : B.ReducedBuilding) (hz : B.IsVertex z) :
    BuildingModelIndex B :=
  BuildingModelIndex.ofFacet ⟨{z}, B.isFacet_singleton_of_isVertex hz⟩

@[simp] theorem coe_vertexModelIndex (z : B.ReducedBuilding) (hz : B.IsVertex z) :
    (B.vertexModelIndex z hz).val = {z} :=
  rfl

/-- At a singleton facet, the family's one-group fixer is precisely the existing
norm-one point stabilizer in the same rational-point group. -/
theorem oneFixer_vertexModelIndex (z : B.ReducedBuilding) (hz : B.IsVertex z) :
    BuildingModelFamily.oneFixer (B.vertexModelIndex z hz) = B.compactStabilizer z := by
  change B.apartment.pointwiseFixer {z} ⊓ Langlands.Plancherel.rationalCommonNormKernel G =
    Langlands.Plancherel.rationalCommonNormKernel G ⊓ B.apartment.reducedFixer z
  rw [B.apartment.pointwiseFixer_singleton, inf_comm]

/-- The full-points clause of a supplied actual family identifies its original
full model image at a vertex, without any change of generic identification. -/
theorem integralPoints_vertexModelIndex
    (family : BuildingModelFamily B ↥𝒪[F])
    (hpoints : ∀ Ω, (family.model Ω).full.integralPoints =
      BuildingModelFamily.oneFixer Ω)
    (z : B.ReducedBuilding) (hz : B.IsVertex z) :
    (family.model (B.vertexModelIndex z hz)).full.integralPoints =
      B.compactStabilizer z := by
  rw [hpoints, B.oneFixer_vertexModelIndex]

end Langlands.Geometry.Building.ValuationBuildingData

namespace Langlands.GroupScheme.IntegralModel.BuildingComparison

open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (M : IntegralModel ↥𝒪[F] F G)

private instance assemblyAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance assemblyGroupTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- Assemble the exact comparison from a metric on the same quotient, a supplied
special apartment point and the original model's stabilizer identity. Vertexhood
and global fixed-point uniqueness follow from the displayed geometric inputs. -/
def ofApartmentSpecialPoint
    (B : ValuationBuildingData G) (metric : B.MetricRealization)
    (R : B.PolysimplicialRealization)
    (hR : AbstractBuilding.IsBuilding R.complex R.apartments)
    (hA : B.SatisfiesApartmentAxioms)
    (hE : RelativeRoot.HasOppositeFactorPairs B.i)
    (hinj : Function.Injective B.apartmentMap)
    (x : B.Apartment) (hx : AffineRootSystem.IsSpecialPoint B.affineRoots x)
    (hM : M.integralPoints = B.compactStabilizer (B.apartmentMap x)) :
    BuildingComparison M := by
  letI := metric.metric
  letI := metric.complete
  letI := metric.isometric
  refine {
    building := B
    metric := metric.metric
    complete := metric.complete
    nonpositivelyCurved := metric.nonpositivelyCurved
    isometric := metric.isometric
    continuous_orbit := metric.continuous_orbit
    point := B.apartmentMap x
    vertex := B.isVertex_apartmentMap
      (AffineRootSystem.isVertex_of_isSpecialPoint hA.isAffineRootSystem_affineRoots hx)
    special := ⟨1, x, one_smul _ _, hx⟩
    integralPoints_eq := hM
    unique_fixed := ?_ }
  intro y hy
  apply R.eq_of_compactStabilizer_fixed_of_isBuilding hR hA.topologyCompatible x ?_ y
    (fun g hg => hy g (hM.symm ▸ hg))
  intro z hz hfixed
  exact B.eq_of_compactStabilizer_fixed_of_isSpecialPoint hA hE hinj hx hz hfixed

@[simp] theorem ofApartmentSpecialPoint_building
    (B : ValuationBuildingData G) (metric : B.MetricRealization)
    (R : B.PolysimplicialRealization)
    (hR : AbstractBuilding.IsBuilding R.complex R.apartments)
    (hA : B.SatisfiesApartmentAxioms)
    (hE : RelativeRoot.HasOppositeFactorPairs B.i)
    (hinj : Function.Injective B.apartmentMap)
    (x : B.Apartment) (hx : AffineRootSystem.IsSpecialPoint B.affineRoots x)
    (hM : M.integralPoints = B.compactStabilizer (B.apartmentMap x)) :
    (ofApartmentSpecialPoint M B metric R hR hA hE hinj x hx hM).building = B :=
  rfl

@[simp] theorem ofApartmentSpecialPoint_point
    (B : ValuationBuildingData G) (metric : B.MetricRealization)
    (R : B.PolysimplicialRealization)
    (hR : AbstractBuilding.IsBuilding R.complex R.apartments)
    (hA : B.SatisfiesApartmentAxioms)
    (hE : RelativeRoot.HasOppositeFactorPairs B.i)
    (hinj : Function.Injective B.apartmentMap)
    (x : B.Apartment) (hx : AffineRootSystem.IsSpecialPoint B.affineRoots x)
    (hM : M.integralPoints = B.compactStabilizer (B.apartmentMap x)) :
    (ofApartmentSpecialPoint M B metric R hR hA hE hinj x hx hM).point = B.apartmentMap x :=
  rfl

/-- Use an actual identity-generic model isomorphism to identify the supplied
model with the full singleton-facet model of the supplied family. All geometric
inputs concern the same quotient, metric, realization and special point. -/
def ofApartmentFamilyModelIso
    (B : ValuationBuildingData G) (metric : B.MetricRealization)
    (R : B.PolysimplicialRealization)
    (hR : AbstractBuilding.IsBuilding R.complex R.apartments)
    (hA : B.SatisfiesApartmentAxioms)
    (hE : RelativeRoot.HasOppositeFactorPairs B.i)
    (hinj : Function.Injective B.apartmentMap)
    (x : B.Apartment) (hx : AffineRootSystem.IsSpecialPoint B.affineRoots x)
    (family : BuildingModelFamily B ↥𝒪[F])
    (hpoints : ∀ Ω, (family.model Ω).full.integralPoints =
      BuildingModelFamily.oneFixer Ω)
    (e : M.Iso
      (family.model (B.vertexModelIndex (B.apartmentMap x)
        (B.isVertex_apartmentMap
          (AffineRootSystem.isVertex_of_isSpecialPoint
            hA.isAffineRootSystem_affineRoots hx)))).full
      (CategoryTheory.Iso.refl G)) :
    BuildingComparison M :=
  ofApartmentSpecialPoint M B metric R hR hA hE hinj x hx
    (e.integralPoints_eq.trans
      (B.integralPoints_vertexModelIndex family hpoints _ _))

end Langlands.GroupScheme.IntegralModel.BuildingComparison
