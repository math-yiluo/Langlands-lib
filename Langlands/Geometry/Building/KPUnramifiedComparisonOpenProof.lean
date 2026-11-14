import Langlands.Geometry.Building.KPUnramifiedFiltrationOpen
import Langlands.Geometry.Building.KPLocalTorusFiltrationOpenness
import Langlands.Geometry.Building.KPUnramifiedComparisonTopology

/-! # Assembly of unramified comparison openness -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

private instance comparisonOpenExtendedAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

set_option maxHeartbeats 1000000 in
/-- Every concrete unramified apartment lift has open comparison subgroups. -/
theorem unramifiedComparisonOpenField :
    UnramifiedComparisonOpenFieldStatement.{u} := by
  intro F _ _ _ _ G _ P _ t L
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine P.centralizer.Z.X.left := by
    have : IsClosedImmersion P.centralizer.j.hom.hom.left := P.centralizer.isClosedSubgroup
    exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left
  let : TopologicalSpace (rationalPoints P.centralizer.Z) :=
    rationalPointTopology F P.centralizer.Z.X
  intro y r
  let : Valued (UnramifiedClosure F) ℝ≥0 := fixedFieldValued F
  let : TopologicalSpace (rationalPoints (baseChanged F (UnramifiedClosure F) G)) :=
    rationalPointTopology (UnramifiedClosure F) (baseChanged F (UnramifiedClosure F) G).X
  let : IsAffine L.buildingData.centralizer.Z.X.left :=
    L.buildingData.centralizerTorus_isAffine L.centralizer_isTorus
  let : TopologicalSpace (rationalPoints L.buildingData.centralizer.Z) :=
    rationalPointTopology (UnramifiedClosure F) L.buildingData.centralizer.Z.X
  apply P.isOpen_unramifiedCentralizerComap
  apply L.buildingData.isOpen_moyPrasad_of_isOpen_torus L.centralizer_isTorus (L.e y) r
  exact isOpen_localTorusFiltration F
    (L.buildingData.centralizerTorus L.centralizer_isTorus)
    L.centralizer_isTorus r

end Langlands.Geometry.Building
