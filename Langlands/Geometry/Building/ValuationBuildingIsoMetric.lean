import Langlands.Geometry.Building.ValuationBuildingIsoTransport
import Langlands.Geometry.Building.MetricRealizationStatement
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # Metric realizations on the actual transported valuation quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {B : ValuationBuildingData G}

private instance sourceAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

private instance targetAffine : IsAffine H.X.left :=
  isAffine_of_isAffineHom H.X.hom

local instance sourceTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

local instance targetTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X

/-- Inverse equivariance uses the actual inverse map on rational points. -/
theorem mapIsoReducedBuildingEquiv_symm_smul (B : ValuationBuildingData G)
    (f : G ≅ H) (h : rationalPoints H) (x : (B.mapIso f).ReducedBuilding) :
    (B.mapIsoReducedBuildingEquiv f).symm (h • x) =
      rationalPoints.map f.inv h • (B.mapIsoReducedBuildingEquiv f).symm x := by
  have hcancel : rationalPoints.map f.hom (rationalPoints.map f.inv h) = h := by
    simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  apply (B.mapIsoReducedBuildingEquiv f).injective
  rw [Equiv.apply_symm_apply, B.mapIsoReducedBuildingEquiv_smul,
    Equiv.apply_symm_apply, hcancel]

namespace MetricRealization

/-- Pull back the original metric by the inverse of the actual quotient equivalence. -/
@[instance_reducible]
def mapIsoMetric (R : B.MetricRealization) (f : G ≅ H) :
    MetricSpace (B.mapIso f).ReducedBuilding := by
  letI := R.metric
  let Q := B.mapIsoReducedBuildingEquiv f
  exact MetricSpace.induced Q.symm Q.symm.injective R.metric

/-- The same quotient equivalence is an isometry for the transported metric. -/
def mapIsoIsometry (R : B.MetricRealization) (f : G ≅ H) :
    letI := R.metric
    letI := R.mapIsoMetric f
    (B.mapIso f).ReducedBuilding ≃ᵢ B.ReducedBuilding := by
  letI := R.metric
  letI := R.mapIsoMetric f
  let Q := B.mapIsoReducedBuildingEquiv f
  exact { Q.symm with
    isometry_toFun := MetricSpace.isometry_induced Q.symm Q.symm.injective }

/-- Transfer all metric witnesses to the same transported quotient and action,
including continuity in the canonical rational-point topology. -/
def mapIso (R : B.MetricRealization) (f : G ≅ H) :
    (B.mapIso f).MetricRealization := by
  letI := R.metric
  letI := R.complete
  letI := R.isometric
  letI := R.mapIsoMetric f
  let Q := B.mapIsoReducedBuildingEquiv f
  let E := R.mapIsoIsometry f
  refine {
    metric := R.mapIsoMetric f
    complete := E.completeSpace
    nonpositivelyCurved := ?_
    isometric := ?_
    continuous_orbit := ?_ }
  · intro x y
    obtain ⟨m, hm⟩ := R.nonpositivelyCurved (Q.symm x) (Q.symm y)
    refine ⟨Q m, fun z => ?_⟩
    change 2 * dist (Q.symm (Q m)) (Q.symm z) ^ 2 +
      (1 / 2) * dist (Q.symm x) (Q.symm y) ^ 2 ≤
        dist (Q.symm x) (Q.symm z) ^ 2 + dist (Q.symm y) (Q.symm z) ^ 2
    simpa only [Q.symm_apply_apply] using hm (Q.symm z)
  · constructor
    intro h
    apply Isometry.of_dist_eq
    intro x y
    change dist (Q.symm (h • x)) (Q.symm (h • y)) = dist (Q.symm x) (Q.symm y)
    rw [B.mapIsoReducedBuildingEquiv_symm_smul,
      B.mapIsoReducedBuildingEquiv_symm_smul, dist_smul]
  · intro x
    have hinv : Continuous
        (rationalPoints.map f.inv : rationalPoints H → rationalPoints G) :=
      continuous_rationalPointMap F f.inv.hom.hom
    have hc := E.symm.continuous.comp ((R.continuous_orbit (Q.symm x)).comp hinv)
    convert hc using 1
    funext h
    change h • x = Q (rationalPoints.map f.inv h • Q.symm x)
    rw [B.mapIsoReducedBuildingEquiv_smul, Q.apply_symm_apply]
    congr 1
    simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

/-- The metric field is exactly the inverse-equivalence induced metric. -/
@[simp] theorem mapIso_metric (R : B.MetricRealization) (f : G ≅ H) :
    (R.mapIso f).metric = R.mapIsoMetric f := rfl

end MetricRealization
end Langlands.Geometry.Building.ValuationBuildingData
