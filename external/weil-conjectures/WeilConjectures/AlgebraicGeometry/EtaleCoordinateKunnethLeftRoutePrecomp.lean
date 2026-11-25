/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
import WeilConjectures.AlgebraicGeometry.EtaleKunnethSymmetricFactorization
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
/-! The pre-composition mate calculation for the left coordinate route. -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.CoordinateTrace
attribute [local instance high] SymmetricCategory.toBraidedCategory
variable (A : Type (u + 1)) [CommRing A]

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory

private theorem symmetry_inv
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (supportedTensorSwapIso C X K M).inv =
      (((derivedTensorSymmetry C X).app M).app K).hom := by
  let := _root_.DerivedCategory.symmetricCategory' (Sheaf X.smallEtaleTopology C)
  simp only [supportedTensorSwapIso, derivedTensorSymmetry,
    _root_.DerivedCategory.canonicalTensorSymmetry,
    BraidedCategory.curriedBraidingNatIso, Iso.app_inv, Iso.app_hom,
    NatIso.ofComponents_inv_app, NatIso.ofComponents_hom_app]
  exact (SymmetricCategory.braiding_swap_eq_inv_braiding K M).symm

private theorem compIso_hom {W X Y : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ Y) (c : W ⟶ Y) (h : p ≫ f = c) :
    (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A) p f c h).hom =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p f).hom ≫
        (eqToIso (congrArg (push A) h)).hom := by
  subst c
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  simp only [rightDerivedLowerStarCompIsoOfComp, conjugateIsoEquiv_apply_hom]
  rw [conjugateEquiv_leftDerivedUpperStarComp_hom]
  simp only [rightDerivedLowerStarComp, Iso.symm_hom, conjugateIsoEquiv_apply_inv,
    Iso.symm_inv]

private theorem compIso_eq {W X Y : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ Y) (c : W ⟶ Y) (h : p ≫ f = c) :
    rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A) p f c h =
      rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p f ≪≫
        eqToIso (congrArg (push A) h) :=
  Iso.ext (compIso_hom A p f c h)

private theorem coordinate_comp_iso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    directComparison A f ≪≫
        rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A)
          (pullback.fst f f) f (pullback.fst f f ≫ f) rfl =
      rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A)
        (pullback.snd f f) f (pullback.fst f f ≫ f) pullback.condition.symm := by
  rw [compIso_eq, compIso_eq]
  simp only [directComparison, eqToIso_refl, Iso.trans_refl, Iso.trans_assoc,
    Iso.symm_self_id]

private theorem coordinate_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (T : DerivedCategoryModule A (pullback f f)) :
    (directComparison A f).hom.app T ≫
        (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A)
          (pullback.fst f f) f (pullback.fst f f ≫ f) rfl).hom.app T =
      (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A)
        (pullback.snd f f) f (pullback.fst f f ≫ f) pullback.condition.symm).hom.app T :=
  congrArg (fun e ↦ e.hom.app T) (coordinate_comp_iso A f)

private theorem orderedProjection_hom [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategoryModule A Y) (E : DerivedCategoryModule A X) :
    (orderedProjectionIso A f K E).hom =
      (supportedTensorSwapIso (ModuleCat.{u + 1} A) Y ((push A f).obj E) K).inv ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app E).app K ≫
        (push A f).map
          (supportedTensorSwapIso (ModuleCat.{u + 1} A) X ((pull A f).obj K) E).inv := by
  rw [symmetry_inv, symmetry_inv]
  rfl

private theorem comparison_inv [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f]
    (L : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X) :
    (comparison A f L M).inv =
      ((derivedTensor (ModuleCat.{u + 1} A) X).map (exchange2 A f M).hom).app
          ((pull A f).obj L) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A)
          (pullback.snd f f)).app ((pull A (pullback.fst f f)).obj M)).app
            ((pull A f).obj L) := by
  rfl

private theorem cancel_iso_app {D E : Type*} [Category D] [Category E]
    {F G : D ⥤ E} (e : F ≅ G) (T : D) {S : E} {a b : S ⟶ F.obj T}
    (h : a ≫ e.hom.app T = b ≫ e.hom.app T) : a = b :=
  (cancel_mono (e.hom.app T)).1 h

/-- The left coordinate route agrees with the projection/base-change factorization before
composing with the canonical direct-image compositor.
Source: the coordinate interchange calculation in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-geo-p1-adjunction/`.
The proof expands the ordered projection, comparison mate and direct compositor, then uses
naturality of the derived tensor comparison and the mate equations for proper exchange.
(auxiliary; not a blueprint node). -/
theorem coordinateKunneth_leftRoute_precomp
    [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (L : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X) :
    (orderedProjectionIso A f ((push A f).obj M) ((pull A f).obj L)).hom ≫
        (push A f).map (comparison A f L M).inv ≫
          (directComparison A f).hom.app _ =
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app M).app
          ((push A f).obj ((pull A f).obj L)) ≫
        (push A f).map
          (tensorBaseChangeMap (ModuleCat.{u + 1} A) (pullback.fst f f)
            (pullback.snd f f) f f
            (pullback.condition (f := f) (g := f)) M ((pull A f).obj L)) := by
  have hk := kunnethMap_symmetricFactorization (ModuleCat.{u + 1} A)
    (pullback.fst f f) (pullback.snd f f) f f (pullback.fst f f ≫ f) rfl
    pullback.condition.symm M ((pull A f).obj L)
  rw [kunnethMap_eq] at hk
  apply cancel_iso_app
    (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A)
      (pullback.fst f f) f (pullback.fst f f ≫ f) rfl)
    (tensor A (pullback f f) ((pull A (pullback.fst f f)).obj M)
      ((pull A (pullback.snd f f)).obj ((pull A f).obj L)))
  simp only [Category.assoc]
  rw [coordinate_comp A f, orderedProjection_hom, comparison_inv]
  simp only [Functor.map_comp, Category.assoc]
  simpa only [pull, push, tensor, exchange2, asIso_hom,
    rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar,
    Functor.postcompose₂_obj_obj_obj_obj, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.comp_obj, Functor.id_obj, Functor.map_comp, Category.assoc] using hk.symm
end AlgebraicGeometry.Etale.CoordinateTrace
