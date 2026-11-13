import Langlands.Geometry.Building.UnramifiedRootJumpDescentStatement
import Langlands.Geometry.Building.BuildingSpecialPointComparison
import Langlands.Geometry.Building.SpecialPointRootJumpDescent
import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction

/-! # Special-point descent from root-jump descent -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- Internal conditional reduction to the all-fixed-points root-jump assertion. -/
def UnramifiedSpecialPointRootJumpReductionStatement : Prop :=
  UnramifiedRootJumpDescentStatement.{u} →
    UnramifiedSpecialPointDescentStatement.{u}

set_option maxHeartbeats 300000 in
/-- Zero-valued lower root-group witnesses supply every direction needed for
specialness in the descended apartment, conditional on the root-jump premise. -/
theorem unramifiedSpecialPointRootJumpReduction :
    UnramifiedSpecialPointRootJumpReductionStatement.{u} := by
  intro hJ F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : Mono iS.hom.hom.left := mono_of_isMaximalSplitTorus hiS
  intro hiT
  let : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro hE D C h6
  dsimp only
  intro DS _ x w hfix hw hx
  have hJfixed := hJ F G hG S iS hiS T iT f hf hiT hE D C h6
  have hJx := hJfixed x hfix
  have hT' : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T).toGrp :=
    hiT.isSplitSubtorus.1
  have : LocallyOfFiniteType G.X.hom := inferInstance
  refine isSpecialPoint_of_rootJumpDescent
    (k := F) (K := inertiaFixedField F) (S := S) (T := T) (G := G)
    (iS := iS) (iT := iT) (f := f) (hS := hiS.isSplitSubtorus.1)
    (hT := hT') (ω := localFieldOrder F)
    (ωK := IntegerValuation.order (MaximalUnramified.valuation F))
    (D := D) (DS := DS) hf x w ?_ ?_
  · exact (D.isSpecialBuildingPoint_apartmentMap_iff
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T) x).mp hx
  conv =>
    intro ψ hzero hnz
    arg 1
    intro a
    arg 1
    intro g
    arg 2
    arg 1
    lhs
    rw [hw]
  -- Normalize instance paths before the restricted definitional comparison.
  dsimp (config := { zeta := false, instances := true }) only
    [Field.toSemifield, Real.instRing, Real.semiring, TensorProduct.addCommGroup] at hJx ⊢
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      with_reducible_and_instances exact hJx

end Langlands.Geometry.Building
