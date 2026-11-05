import Langlands.Geometry.Building.ValuationBuildingAxioms
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Mathlib.Topology.LocallyConstant.Basic

/-! # Orbit continuity from open norm-one point stabilizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

private instance orbitAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

local instance orbitGroupTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

/-- Every existing norm-one point stabilizer is open in the canonical
rational-point topology. This isolates the topological part of
`HasBoundedOpenStabilizers`. -/
def HasOpenCompactStabilizers : Prop :=
  ∀ x : B.ReducedBuilding,
    IsOpen (B.compactStabilizer x : Set (rationalPoints G))

/-- The bounded-open-stabilizer condition contains the open-stabilizer
condition. -/
theorem hasOpenCompactStabilizers_of_hasBoundedOpenStabilizers
    (hB : B.HasBoundedOpenStabilizers) : B.HasOpenCompactStabilizers :=
  fun x => (hB x).1

/-- Openness of the existing norm-one point stabilizer makes the existing orbit
map locally constant in exactly the canonical rational-point topology. -/
theorem isLocallyConstant_orbit_of_isOpen_compactStabilizer
    (x : B.ReducedBuilding)
    (hx : IsOpen (B.compactStabilizer x : Set (rationalPoints G))) :
    IsLocallyConstant (fun g : rationalPoints G => g • x) := by
  let : Smooth G.X.hom := B.isConnectedReductive.smooth
  let : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hopen : IsOpen {h : rationalPoints G | g⁻¹ * h ∈ B.compactStabilizer x} :=
    hx.preimage (continuous_const.mul continuous_id)
  have hneighborhood :
      {h : rationalPoints G | g⁻¹ * h ∈ B.compactStabilizer x} ∈ 𝓝 g :=
    hopen.mem_nhds (by simp)
  filter_upwards [hneighborhood] with h hh
  have hfix := (B.mem_compactStabilizer.mp hh).2
  have heq := congrArg (fun y : B.ReducedBuilding => g • y) hfix
  simpa only [smul_smul, mul_inv_cancel_left] using heq

/-- Open norm-one stabilizers give locally constant orbits for the existing
quotient action. -/
theorem isLocallyConstant_orbit_of_hasOpenCompactStabilizers
    (hB : B.HasOpenCompactStabilizers) (x : B.ReducedBuilding) :
    IsLocallyConstant (fun g : rationalPoints G => g • x) :=
  B.isLocallyConstant_orbit_of_isOpen_compactStabilizer x (hB x)

/-- The existing bounded-open-stabilizer axiom suffices for local constancy of
every orbit map; only its openness clause is used. -/
theorem isLocallyConstant_orbit_of_hasBoundedOpenStabilizers
    (hB : B.HasBoundedOpenStabilizers) (x : B.ReducedBuilding) :
    IsLocallyConstant (fun g : rationalPoints G => g • x) :=
  B.isLocallyConstant_orbit_of_hasOpenCompactStabilizers
    (B.hasOpenCompactStabilizers_of_hasBoundedOpenStabilizers hB) x

/-- Open norm-one stabilizers give continuous orbit maps for every topology on
this same quotient. -/
theorem continuous_orbit_of_hasOpenCompactStabilizers
    [TopologicalSpace B.ReducedBuilding]
    (hB : B.HasOpenCompactStabilizers) (x : B.ReducedBuilding) :
    Continuous (fun g : rationalPoints G => g • x) :=
  (B.isLocallyConstant_orbit_of_hasOpenCompactStabilizers hB x).continuous

/-- Every topology on this same quotient, in particular a constructed building
metric, gives continuous orbit maps when the norm-one stabilizers are open. -/
theorem continuous_orbit_of_hasBoundedOpenStabilizers
    [TopologicalSpace B.ReducedBuilding]
    (hB : B.HasBoundedOpenStabilizers) (x : B.ReducedBuilding) :
    Continuous (fun g : rationalPoints G => g • x) :=
  B.continuous_orbit_of_hasOpenCompactStabilizers
    (B.hasOpenCompactStabilizers_of_hasBoundedOpenStabilizers hB) x

end Langlands.Geometry.Building.ValuationBuildingData
