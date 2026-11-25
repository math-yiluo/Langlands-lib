/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees
/-! The right coordinate route is the canonical Kunneth map after composition. -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.CoordinateTrace
attribute [local instance high] SymmetricCategory.toBraidedCategory
variable (A : Type (u + 1)) [CommRing A]

/-- The projection/exchange route identifies with the canonical Kunneth map after
composing `R p₁_*` and `R f_*`.  This is the second mate calculation in the
coordinate interchange argument.
Source: the coordinate interchange calculation in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-geo-p1-adjunction/`.
(auxiliary; not a blueprint node).
-/
theorem coordinateKunneth_rightRoute_comp_kunneth
    [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (L : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X) :
    (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app M).app
          ((push A f).obj ((pull A f).obj L)) ≫
        (push A f).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
              (exchange1 A f ((pull A f).obj L)).hom ≫
            (orderedProjectionIso A (pullback.fst f f) M
              ((pull A (pullback.snd f f)).obj ((pull A f).obj L))).hom)) ≫
        (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A)
          (pullback.fst f f) f (pullback.fst f f ≫ f) rfl).hom.app _ =
      kunnethMap (ModuleCat.{u + 1} A) (pullback.fst f f) (pullback.snd f f)
        f f (pullback.fst f f ≫ f) rfl (pullback.condition (f := f) (g := f)).symm
        M ((pull A f).obj L) := by
  let := _root_.DerivedCategory.symmetricCategory'
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
  let := _root_.DerivedCategory.symmetricCategory'
    (Sheaf (pullback f f).smallEtaleTopology (ModuleCat.{u + 1} A))
  simpa only [pull, push, tensor, derivedTensorRightDerivedLowerStar, Functor.comp_obj,
    derivedTensor, MonoidalCategory.curriedTensor_obj_obj,
    orderedProjectionIso, swap, exchange1,
    Iso.trans_hom, Iso.app_hom,
    asIso_hom, Functor.mapIso_hom, derivedTensorSymmetry,
    _root_.DerivedCategory.canonicalTensorSymmetry,
    BraidedCategory.curriedBraidingNatIso, NatIso.ofComponents_hom_app,
    Category.assoc, SymmetricCategory.braiding_swap_eq_inv_braiding] using
      (kunnethMap_eq_of_isPullback (ModuleCat.{u + 1} A)
        (pullback.fst f f) (pullback.snd f f) f f (pullback.fst f f ≫ f)
        rfl (pullback.condition (f := f) (g := f)).symm M ((pull A f).obj L)).symm
end AlgebraicGeometry.Etale.CoordinateTrace
