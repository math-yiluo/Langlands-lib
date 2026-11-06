import Langlands.Geometry.Building.MetricRealizationStatement
import Langlands.GroupScheme.IntegralModel.BuildingComparison

/-! # Transport of metrics and supplied-model comparisons on actual building quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {B₁ B₂ : ValuationBuildingData G}

private instance transportGenericAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance transportGenericTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- Pull back a supplied complete NPC metric along an equivalence intertwining
exactly the original action of the same rational-point group. -/
def MetricRealization.pullback (R : B₂.MetricRealization)
    (e : B₁.ReducedBuilding ≃ B₂.ReducedBuilding)
    (he : ∀ (g : rationalPoints G) (x : B₁.ReducedBuilding), e (g • x) = g • e x) :
    B₁.MetricRealization := by
  letI := R.metric
  letI := R.complete
  letI := R.isometric
  letI : MetricSpace B₁.ReducedBuilding := MetricSpace.induced e e.injective R.metric
  let E : B₁.ReducedBuilding ≃ᵢ B₂.ReducedBuilding :=
    { toEquiv := e
      isometry_toFun := MetricSpace.isometry_induced e e.injective }
  letI : CompleteSpace B₁.ReducedBuilding := E.completeSpace
  letI : IsIsometricSMul (rationalPoints G) B₁.ReducedBuilding :=
    ⟨fun g => Isometry.of_dist_eq fun x y => by
      change dist (e (g • x)) (e (g • y)) = dist (e x) (e y)
      rw [he, he, dist_smul]⟩
  refine { nonpositivelyCurved := ?_, continuous_orbit := ?_ }
  · intro x y
    obtain ⟨m, hm⟩ := R.nonpositivelyCurved (e x) (e y)
    refine ⟨e.symm m, fun z => ?_⟩
    change 2 * dist (e (e.symm m)) (e z) ^ 2 +
      (1 / 2) * dist (e x) (e y) ^ 2 ≤
        dist (e x) (e z) ^ 2 + dist (e y) (e z) ^ 2
    simpa only [Equiv.apply_symm_apply] using hm (e z)
  · intro x
    have h := E.symm.continuous.comp (R.continuous_orbit (e x))
    convert h using 1
    funext g
    apply e.injective
    exact (he g x).trans (e.apply_symm_apply _).symm

/-- The transported metric is precisely the pullback metric, with no rescaling. -/
theorem MetricRealization.pullback_dist (R : B₂.MetricRealization)
    (e : B₁.ReducedBuilding ≃ B₂.ReducedBuilding)
    (he : ∀ (g : rationalPoints G) (x : B₁.ReducedBuilding), e (g • x) = g • e x)
    (x y : B₁.ReducedBuilding) :
    @dist _ (R.pullback e he).metric.toDist x y = @dist _ R.metric.toDist (e x) (e y) :=
  rfl

/-- Equivariance for the same ambient group identifies its actual norm-one
point stabilizers as equal subgroups of that group. -/
theorem compactStabilizer_eq_of_equivariant
    (e : B₁.ReducedBuilding ≃ B₂.ReducedBuilding)
    (he : ∀ (g : rationalPoints G) (x : B₁.ReducedBuilding), e (g • x) = g • e x)
    (x : B₁.ReducedBuilding) :
    B₁.compactStabilizer x = B₂.compactStabilizer (e x) := by
  apply Subgroup.ext
  intro g
  rw [B₁.mem_compactStabilizer, B₂.mem_compactStabilizer, ← he]
  exact and_congr_right fun _ => e.injective.eq_iff.symm

end Langlands.Geometry.Building.ValuationBuildingData

namespace Langlands.GroupScheme.IntegralModel.BuildingComparison

open Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {M : IntegralModel ↥𝒪[F] F G}

/-- Transfer a supplied model's comparison to another actual quotient through a
same-group equivariant equivalence, retaining explicit vertex and special-point
evidence at the inverse image of its original point. -/
def pullback (D : BuildingComparison M) (B : ValuationBuildingData G)
    (e : B.ReducedBuilding ≃ D.building.ReducedBuilding)
    (he : ∀ (g : rationalPoints G) (x : B.ReducedBuilding), e (g • x) = g • e x)
    (hvertex : B.IsVertex (e.symm D.point))
    (hspecial : B.IsSpecialPoint (e.symm D.point)) : BuildingComparison M := by
  let R : D.building.MetricRealization :=
    { metric := D.metric
      complete := D.complete
      nonpositivelyCurved := D.nonpositivelyCurved
      isometric := D.isometric
      continuous_orbit := D.continuous_orbit }
  let S := R.pullback e he
  refine
    { building := B
      metric := S.metric
      complete := S.complete
      nonpositivelyCurved := S.nonpositivelyCurved
      isometric := S.isometric
      continuous_orbit := S.continuous_orbit
      point := e.symm D.point
      vertex := hvertex
      special := hspecial
      integralPoints_eq := ?_
      unique_fixed := ?_ }
  · rw [D.integralPoints_eq]
    simpa only [Equiv.apply_symm_apply] using
      (ValuationBuildingData.compactStabilizer_eq_of_equivariant e he (e.symm D.point)).symm
  · intro y hy
    apply e.injective
    rw [Equiv.apply_symm_apply]
    apply D.unique_fixed
    intro g hg
    rw [← he, hy g hg]

/-- The comparison uses exactly the supplied target building data. -/
@[simp] theorem pullback_building (D : BuildingComparison M) (B : ValuationBuildingData G)
    (e : B.ReducedBuilding ≃ D.building.ReducedBuilding)
    (he : ∀ (g : rationalPoints G) (x : B.ReducedBuilding), e (g • x) = g • e x)
    (hvertex : B.IsVertex (e.symm D.point))
    (hspecial : B.IsSpecialPoint (e.symm D.point)) :
    (D.pullback B e he hvertex hspecial).building = B := rfl

/-- The distinguished point is the exact inverse image of the supplied point. -/
@[simp] theorem pullback_point (D : BuildingComparison M) (B : ValuationBuildingData G)
    (e : B.ReducedBuilding ≃ D.building.ReducedBuilding)
    (he : ∀ (g : rationalPoints G) (x : B.ReducedBuilding), e (g • x) = g • e x)
    (hvertex : B.IsVertex (e.symm D.point))
    (hspecial : B.IsSpecialPoint (e.symm D.point)) :
    (D.pullback B e he hvertex hspecial).point = e.symm D.point := rfl

end Langlands.GroupScheme.IntegralModel.BuildingComparison
