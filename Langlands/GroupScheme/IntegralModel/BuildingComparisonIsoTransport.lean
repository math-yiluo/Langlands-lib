import Langlands.GroupScheme.IntegralModel.BuildingComparison
import Langlands.GroupScheme.IntegralModel.InducedGenericIso
import Langlands.Geometry.Building.ValuationBuildingIsoGeometry
import Langlands.Geometry.Building.ValuationBuildingIsoMetric

/-! # Actual building comparisons through integral-model isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.AlgebraicGeometry.PointTopology Langlands.Geometry.Building

namespace Langlands.GroupScheme.IntegralModel.BuildingComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {M : IntegralModel ↥𝒪[F] F G} {N : IntegralModel ↥𝒪[F] F H}

private instance sourceAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

private instance targetAffine : IsAffine H.X.left :=
  isAffine_of_isAffineHom H.X.hom

local instance sourceTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

local instance targetTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X

omit [IsAffineHom H.X.hom] in
/-- Extract exactly the supplied metric realization on the original quotient. -/
def toMetricRealization (D : BuildingComparison M) : D.building.MetricRealization where
  metric := D.metric
  complete := D.complete
  nonpositivelyCurved := D.nonpositivelyCurved
  isometric := D.isometric
  continuous_orbit := D.continuous_orbit

/-- Transport a supplied comparison through the actual compatible integral-model
isomorphism and the actual quotient equivalence induced by its generic map. -/
def mapIso (D : BuildingComparison M) {f : G ≅ H} (e : M.Iso N f) :
    BuildingComparison N := by
  let B := D.building
  let Q := B.mapIsoReducedBuildingEquiv f
  let R := D.toMetricRealization.mapIso f
  refine {
    building := B.mapIso f
    metric := R.metric
    complete := R.complete
    nonpositivelyCurved := R.nonpositivelyCurved
    isometric := R.isometric
    continuous_orbit := R.continuous_orbit
    point := Q D.point
    vertex := (B.isVertex_mapIso_iff f D.point).mpr D.vertex
    special := (B.isSpecialPoint_mapIso_iff f D.point).mpr D.special
    integralPoints_eq := ?_
    unique_fixed := ?_ }
  · rw [← e.map_integralPoints, D.integralPoints_eq]
    exact B.map_compactStabilizer_mapIso f D.point
  · intro y hy
    have hfixed : ∀ g : rationalPoints G, g ∈ M.integralPoints →
        g • Q.symm y = Q.symm y := by
      intro g hg
      apply Q.injective
      rw [B.mapIsoReducedBuildingEquiv_smul, Q.apply_symm_apply]
      exact hy _ (e.toHom.map_mem_integralPoints hg)
    have hpoint := D.unique_fixed (Q.symm y) hfixed
    simpa only [Q.apply_symm_apply] using congrArg Q hpoint

/-- The building is exactly the transported full valuation-building datum. -/
@[simp] theorem mapIso_building (D : BuildingComparison M) {f : G ≅ H}
    (e : M.Iso N f) :
    (D.mapIso e).building = D.building.mapIso f := rfl

/-- The distinguished point uses the same quotient map as the metric and action. -/
@[simp] theorem mapIso_point (D : BuildingComparison M) {f : G ≅ H}
    (e : M.Iso N f) :
    (D.mapIso e).point = D.building.mapIsoReducedBuildingEquiv f D.point := rfl

/-- An abstract integral isomorphism transports the comparison using its actual
induced generic map and both original generic identifications. -/
def ofGroupIso (D : BuildingComparison M) (e : M.group ≅ N.group) :
    BuildingComparison N :=
  D.mapIso (Iso.ofGroupIso M N e)

/-- This abstract adapter retains the actual induced generic building transport. -/
@[simp] theorem ofGroupIso_building (D : BuildingComparison M)
    (e : M.group ≅ N.group) :
    (D.ofGroupIso e).building = D.building.mapIso (M.inducedGenericIso N e) := rfl

end Langlands.GroupScheme.IntegralModel.BuildingComparison
