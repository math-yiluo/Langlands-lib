/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProperSupportedKunnethRoute
import WeilConjectures.AlgebraicGeometry.EtaleKunnethTensorSymmetry
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees

/-! # Symmetric normal form for the ordinary Kunneth map

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, first coordinate triangle.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local instance high] SymmetricCategory.toBraidedCategory

section General

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [UpperStarPreservesFlat C]

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensorSymmetry supportedTensorSwapIso kunnethMap
  derivedBaseChangeMap rightDerivedLowerStarProjectionMap

attribute [local implicit_reducible] derivedTensorRight
  derivedTensorRightDerivedLowerStar rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar

section ProjectionNaturality

attribute [local irreducible] derivedTensor

/-- Naturality in the outside coefficient of the ordinary projection map.
Source: the projection factor in the first coordinate triangle
(auxiliary; not a blueprint node). -/
@[reassoc]
theorem kunnethProjection_naturality_right {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    {M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)} (a : M ⟶ N) :
    ((derivedTensor C Y).obj ((lowerStar C f).rightDerivedFunctor.obj E)).map a ≫
        ((rightDerivedLowerStarProjectionMap C f).app E).app N =
      ((rightDerivedLowerStarProjectionMap C f).app E).app M ≫
        (lowerStar C f).rightDerivedFunctor.map
          (((derivedTensor C X).obj E).map
            ((upperStar C f).leftDerivedFunctor.map a)) := by
  simpa only [derivedTensorRightDerivedLowerStar,
    rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar,
    Functor.postcompose₂, Functor.whiskeringLeft₂, Functor.whiskeringLeft,
    Functor.whiskeringRight, Functor.comp_obj, Functor.id_obj,
    Functor.comp_map, Functor.id_map] using
      ((rightDerivedLowerStarProjectionMap C f).app E).naturality a

end ProjectionNaturality

/-- The ordinary Kunneth map in the symmetric projection/exchange normal form.
Source: the common-counit calculation in the first coordinate triangle
(auxiliary; not a blueprint node).

Proof: cancel the direct image of the kernel swap. Kunneth tensor symmetry and
the existing flipped projection/exchange factorization give the two paths.
Move the kernel swap across the ordinary compositor by naturality. Naturality
of the canonical signed braiding puts the two projection factors in the stated
order, and involutivity cancels the two kernel symmetries. -/
theorem kunnethMap_symmetricFactorization {S X Y W : Scheme.{u}}
    (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (h : W ⟶ S)
    (hp : p ≫ f = h) (hq : q ≫ g = h)
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    kunnethMap C p q f g h hp hq E K =
      (supportedTensorSwapIso C S
        ((lowerStar C g).rightDerivedFunctor.obj K)
        ((lowerStar C f).rightDerivedFunctor.obj E)).inv ≫
        ((rightDerivedLowerStarProjectionMap C g).app K).app
          ((lowerStar C f).rightDerivedFunctor.obj E) ≫
        (lowerStar C g).rightDerivedFunctor.map
          ((supportedTensorSwapIso C Y
            ((upperStar C g).leftDerivedFunctor.obj
              ((lowerStar C f).rightDerivedFunctor.obj E)) K).inv ≫
            ((derivedTensor C Y).map
              ((derivedBaseChangeMap C
                (CommSq.mk (hp.trans hq.symm))).app E)).app K ≫
            ((rightDerivedLowerStarProjectionMap C q).app
              ((upperStar C p).leftDerivedFunctor.obj E)).app K) ≫
        (rightDerivedLowerStarCompIsoOfComp
          C q g h hq).hom.app _ := by
  let := _root_.DerivedCategory.symmetricCategory'
    (Sheaf S.smallEtaleTopology C)
  let := _root_.DerivedCategory.symmetricCategory'
    (Sheaf Y.smallEtaleTopology C)
  let := _root_.DerivedCategory.symmetricCategory'
    (Sheaf W.smallEtaleTopology C)
  let sw := supportedTensorSwapIso C W
    ((upperStar C p).leftDerivedFunctor.obj E)
    ((upperStar C q).leftDerivedFunctor.obj K)
  have hs := kunnethMap_tensorSymmetry C p q f g h hp hq E K
  apply (cancel_mono ((lowerStar C h).rightDerivedFunctor.map
    sw.hom)).1
  rw [hs]
  erw [kunnethMap_eq_of_isPullback C q p g f h hq hp K E]
  simp only [Category.assoc]
  erw [← (rightDerivedLowerStarCompIsoOfComp
    C q g h hq).hom.naturality sw.hom]
  simp only [sw, supportedTensorSwapIso, derivedTensorSymmetry,
    _root_.DerivedCategory.canonicalTensorSymmetry]
  dsimp only [BraidedCategory.curriedBraidingNatIso, Iso.app, NatIso.ofComponents]
  simp only [← SymmetricCategory.braiding_swap_eq_inv_braiding]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, derivedTensor,
    curriedTensor_map_app, curriedTensor_obj_map, Category.assoc]
  erw [BraidedCategory.braiding_naturality_right_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end General

end AlgebraicGeometry.Etale
