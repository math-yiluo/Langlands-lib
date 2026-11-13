import Langlands.Geometry.Building.KPZeroDatumConstruction
import Langlands.GroupScheme.SimplyConnected.DerivedCoverProof

/-! # Zero-subgroup data for a connected reductive unramified group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Choose an actual derived cover and use it to construct all the zero-datum
choices for a supplied connected reductive group over the unramified field. -/
def ofConnectedReductive
    (H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
    (hH : IsConnectedReductive H) : UnramifiedZeroDatum F H := by
  let hcover := simplyConnectedDerivedCoverExistence (UnramifiedClosure F) H hH
  let D := hcover.choose
  let C := hcover.choose_spec.choose
  let d := hcover.choose_spec.choose_spec.choose
  let π := hcover.choose_spec.choose_spec.choose_spec.choose
  exact ofDerivedCover d π hcover.choose_spec.choose_spec.choose_spec.choose_spec

end Langlands.Geometry.Building.UnramifiedZeroDatum
