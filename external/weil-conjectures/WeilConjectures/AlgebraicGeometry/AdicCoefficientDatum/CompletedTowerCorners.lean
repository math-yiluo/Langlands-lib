/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourArrows
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits

/-! # The specified strict four towers and arrows

These are the original tower constructions, separated from their compatibility theorem
so the existing strict-mate normalization theorem can use them independently.
Source: blueprint proper base change, tower compatibility
(blueprint: def-weil-pbc-completed-four-towers).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U V : Scheme.{t}} (f : U ⟶ V)

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

/-- The strict four corner towers, formed before taking Rlim. The third corner uses
ordinary pullback. Source: blueprint tower compatibility
(blueprint: def-weil-pbc-completed-four-towers). -/
def AdicCoefficientDatum.fourTowerCorners (K : d.derived X) :
    Fin 4 → DerivedCategory (d.towers Y') :=
  ![(d.towerPull g).obj ((completedReductionTower Y d).obj ((d.push f).obj K)),
    (d.towerPull g).obj ((d.towerPush f).obj
      ((completedReductionTower X d).obj K)),
    (completedReductionTower Y' d).obj ((d.push f').obj ((d.pull g').obj K)),
    (d.towerPush f').obj ((d.towerPull g').obj
      ((completedReductionTower X d).obj K))]

/-- The specified strict projection h, including the canonical source identification.
Source: blueprint tower compatibility (blueprint: def-weil-pbc-completed-four-towers). -/
def AdicCoefficientDatum.towerH (K : d.derived X) :
    d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 0 ≅
      d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 1 :=
  (d.towerPull g).mapIso (asIso (d.towerProjection f K))

/-- The specified strict projection h', followed by the inverse pullback/reduction map.
Source: blueprint tower compatibility (blueprint: def-weil-pbc-completed-four-towers). -/
def AdicCoefficientDatum.towerH' (K : d.derived X) :
    d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 2 ≅
      d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 3 :=
  asIso (d.towerProjection f' ((d.pull g').obj K)) ≪≫
    (d.towerPush f').mapIso ((d.reductionTowerPullbackIso g').symm.app K)

/-- The strict reduction of ambient exchange, with the source chi retained.
Source: blueprint tower compatibility (blueprint: def-weil-pbc-completed-four-towers). -/
def AdicCoefficientDatum.towerV (K : d.derived X) :
    d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 0 ⟶
      d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 2 :=
  (d.reductionTowerPullbackIso g).hom.app ((d.push f).obj K) ≫
    (completedReductionTower Y' d).map ((d.integralExchange sq).app K)

/-- The specified strict lift of finite exchange. This is the projection-formula
realization H' R(e) H inverse; equality of its evaluations does not define its lift.
Source: blueprint tower compatibility, as expanded in strict-tower mate normalization
(blueprint: def-weil-pbc-completed-four-towers). -/
def AdicCoefficientDatum.towerV' (K : d.derived X) :
    d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 1 ⟶
      d.fourTowerCorners (f := f) (f' := f') (g := g) (g' := g') K 3 :=
  (d.towerH (f := f) (f' := f') (g := g) (g' := g') K).inv ≫
    d.towerV sq K ≫ (d.towerH' (f := f) (f' := f') (g := g) (g' := g') K).hom

end AlgebraicGeometry.Scheme
