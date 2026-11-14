import Langlands.Geometry.Building.KPUnramifiedComparisonFieldStatements
import Langlands.Geometry.Building.KPZeroTopologyDescent
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # Continuity for restriction to the downstairs centralizer -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

private instance ambientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
private instance centralizerAffine : IsAffine P.centralizer.Z.X.left := by
  have : IsClosedImmersion P.centralizer.j.hom.hom.left := P.centralizer.isClosedSubgroup
  exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left

local instance comparisonValued : Valued (UnramifiedClosure F) ℝ≥0 := fixedFieldValued F
local instance ambientTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance centralizerTopology : TopologicalSpace (rationalPoints P.centralizer.Z) :=
  rationalPointTopology F P.centralizer.Z.X
local instance extendedTopology :
    TopologicalSpace (rationalPoints (baseChanged F (UnramifiedClosure F) G)) :=
  rationalPointTopology (UnramifiedClosure F) (baseChanged F (UnramifiedClosure F) G).X

set_option maxHeartbeats 1000000 in
/-- The actual centralizer inclusion followed by unramified scalar extension,
with the canonical rational-point topologies. -/
def unramifiedCentralizerContinuousHom :
    rationalPoints P.centralizer.Z →ₜ*
      rationalPoints (baseChanged F (UnramifiedClosure F) G) := by
  have hJ : Continuous (rationalPoints.map P.centralizer.j) :=
    continuous_rationalPointMap F P.centralizer.j.hom.hom
  have hExt : Continuous (rationalExtend F (UnramifiedClosure F) G) :=
    (unramifiedRationalExtensionContinuousHom F G).continuous
  exact
    { toMonoidHom := (rationalExtend F (UnramifiedClosure F) G).comp
        (rationalPoints.map P.centralizer.j)
      continuous_toFun := by
        change Continuous (fun z : rationalPoints P.centralizer.Z =>
          rationalExtend F (UnramifiedClosure F) G (rationalPoints.map P.centralizer.j z))
        exact hExt.comp hJ }

@[simp] theorem unramifiedCentralizerContinuousHom_apply (z : rationalPoints P.centralizer.Z) :
    P.unramifiedCentralizerContinuousHom z =
      rationalExtend F (UnramifiedClosure F) G (rationalPoints.map P.centralizer.j z) := rfl

/-- Restricting an open upstairs subgroup to the downstairs centralizer is open. -/
theorem isOpen_unramifiedCentralizerComap
    (Q : Subgroup (rationalPoints (baseChanged F (UnramifiedClosure F) G)))
    (hQ : IsOpen (Q : Set (rationalPoints (baseChanged F (UnramifiedClosure F) G)))) :
    IsOpen (((Q.comap (rationalExtend F (UnramifiedClosure F) G)).comap
      (rationalPoints.map P.centralizer.j)) : Set (rationalPoints P.centralizer.Z)) :=
  hQ.preimage P.unramifiedCentralizerContinuousHom.continuous

end Langlands.Geometry.Building.ParahoricBuildingData
