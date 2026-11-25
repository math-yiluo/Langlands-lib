/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
import WeilConjectures.AlgebraicGeometry.EtaleCoordinateKunnethLeftRoutePrecomp
/-! The left coordinate route is the canonical Kunneth map after composition. -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.CoordinateTrace
variable (A : Type (u + 1)) [CommRing A]

/-- The ordered-projection/comparison route identifies with the canonical Kunneth map
after composing `R p₁_*` and `R f_*`.  This is the first mate calculation in the
coordinate interchange argument.
Source: the coordinate interchange calculation in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-geo-p1-adjunction/`.
(auxiliary; not a blueprint node).
-/
theorem coordinateKunneth_leftRoute_comp_kunneth
    [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (L : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X) :
    ((orderedProjectionIso A f ((push A f).obj M) ((pull A f).obj L)).hom ≫
        (push A f).map (comparison A f L M).inv ≫
          (directComparison A f).hom.app _ ) ≫
        (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A)
          (pullback.fst f f) f (pullback.fst f f ≫ f) rfl).hom.app _ =
      kunnethMap (ModuleCat.{u + 1} A) (pullback.fst f f) (pullback.snd f f)
        f f (pullback.fst f f ≫ f) rfl (pullback.condition (f := f) (g := f)).symm
        M ((pull A f).obj L) := by
  rw [kunnethMap_eq]
  conv_rhs => rw [← Category.assoc]
  change _ ≫ (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A)
      (pullback.fst f f) f (pullback.fst f f ≫ f) rfl).hom.app
      (tensor A (pullback f f) ((pull A (pullback.fst f f)).obj M)
        ((pull A (pullback.snd f f)).obj ((pull A f).obj L))) = _ ≫
    (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A)
      (pullback.fst f f) f (pullback.fst f f ≫ f) rfl).hom.app
      (tensor A (pullback f f) ((pull A (pullback.fst f f)).obj M)
        ((pull A (pullback.snd f f)).obj ((pull A f).obj L)))
  exact (cancel_mono
    ((rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A)
      (pullback.fst f f) f (pullback.fst f f ≫ f) rfl).hom.app
      (tensor A (pullback f f) ((pull A (pullback.fst f f)).obj M)
        ((pull A (pullback.snd f f)).obj ((pull A f).obj L))))).2
    (coordinateKunneth_leftRoute_precomp A f L M)
end AlgebraicGeometry.Etale.CoordinateTrace
