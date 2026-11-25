/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProperSupportedKunnethRoute
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees

/-! # Tensor symmetry of the native etale Kunneth morphism

Source: the common-counit computation in the first triangle of
sec-six-functors-basics/sk-prop-geo-p1-adjunction/thm-amb-p1-adjunction.proof.md.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [UpperStarPreservesFlat C]

private theorem kunneth_transpose {S X Y W : Scheme.{u}}
    (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (c : W ⟶ S)
    (hp : p ≫ f = c) (hq : q ≫ g = c)
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    ((derivedUpperStarLowerStarAdjunction C c).homEquiv _ _).symm
        (kunnethMap C p q f g c hp hq E K) =
      ((leftDerivedUpperStarTensorComparison C c).app
        ((lowerStar C f).rightDerivedFunctor.obj E)).app
          ((lowerStar C g).rightDerivedFunctor.obj K) ≫
        ((derivedTensor C W).map
          ((leftDerivedUpperStarComp C p f c hp.symm).hom.app _ ≫
            (upperStar C p).leftDerivedFunctor.map
              ((derivedUpperStarLowerStarAdjunction C f).counit.app E))).app _ ≫
        ((derivedTensor C W).obj _).map
          ((leftDerivedUpperStarComp C q g c hq.symm).hom.app _ ≫
            (upperStar C q).leftDerivedFunctor.map
              ((derivedUpperStarLowerStarAdjunction C g).counit.app K)) := by
  rw [kunnethMap, Equiv.symm_apply_apply]
  rw [← reassoc_of% (leftDerivedUpperStarTensorComparison_comp_derivedTensor C p f c
    hp.symm ((lowerStar C f).rightDerivedFunctor.obj E)
      ((lowerStar C g).rightDerivedFunctor.obj K))]
  simp only [derivedTensor, curriedTensor_map_app, curriedTensor_obj_map,
    Category.assoc, whiskerLeft_comp, comp_whiskerRight]
  rw [whisker_exchange_assoc]
  simp only [← whiskerLeft_comp, Iso.hom_inv_id_app_assoc]

/-- Swapping the two external factors commutes with the canonical Kunneth morphism.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, common pullback counits;
Stacks Tags 0B56 and 06YU (auxiliary; not a blueprint node).

Proof: transpose both sides along the native pullback/direct-image adjunction for c.
The pullback tensor comparison for c is followed by the tensor of the two maps
c* Rf* E to p* E and c* Rg* K to q* K, each given by the pullback compositor
and the corresponding original counit. The tensor comparison is braided and the
braiding is natural with respect to these two maps. Their naturality square is
exactly the transposed equality. Injectivity of the adjunction gives the result.
No cartesianness, properness or invertibility of projection maps is used. -/
theorem kunnethMap_tensorSymmetry {S X Y W : Scheme.{u}}
    (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (c : W ⟶ S)
    (hp : p ≫ f = c) (hq : q ≫ g = c)
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    kunnethMap C p q f g c hp hq E K ≫
        (lowerStar C c).rightDerivedFunctor.map
          (supportedTensorSwapIso C W
            ((upperStar C p).leftDerivedFunctor.obj E)
              ((upperStar C q).leftDerivedFunctor.obj K)).hom =
      (supportedTensorSwapIso C S
        ((lowerStar C f).rightDerivedFunctor.obj E)
          ((lowerStar C g).rightDerivedFunctor.obj K)).hom ≫
        kunnethMap C q p g f c hq hp K E := by
  apply ((derivedUpperStarLowerStarAdjunction C c).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm, kunneth_transpose]
  erw [kunneth_transpose C q p g f c hq hp K E]
  let := _root_.DerivedCategory.braidedCategory' (Sheaf S.smallEtaleTopology C)
  let := _root_.DerivedCategory.braidedCategory' (Sheaf W.smallEtaleTopology C)
  simp only [supportedTensorSwapIso, derivedTensorSymmetry,
    _root_.DerivedCategory.canonicalTensorSymmetry, BraidedCategory.curriedBraidingNatIso,
    Iso.app_hom,
    NatIso.ofComponents_hom_app, Category.assoc]
  rw [leftDerivedUpperStar_map_braiding_hom_comp_tensorComparison_assoc]
  let a := (leftDerivedUpperStarComp C p f c hp.symm).hom.app
    ((lowerStar C f).rightDerivedFunctor.obj E) ≫
      (upperStar C p).leftDerivedFunctor.map
        ((derivedUpperStarLowerStarAdjunction C f).counit.app E)
  let b := (leftDerivedUpperStarComp C q g c hq.symm).hom.app
    ((lowerStar C g).rightDerivedFunctor.obj K) ≫
      (upperStar C q).leftDerivedFunctor.map
        ((derivedUpperStarLowerStarAdjunction C g).counit.app K)
  simpa only [a, b, Functor.id_obj, Functor.flip_obj_obj, curriedTensor_obj_obj,
    derivedTensor, curriedTensor_map_app, curriedTensor_obj_map,
    MonoidalCategory.tensorHom_def, Category.assoc] using
      congrArg (fun k ↦
        ((leftDerivedUpperStarTensorComparison C c).app
          ((lowerStar C f).rightDerivedFunctor.obj E)).app
            ((lowerStar C g).rightDerivedFunctor.obj K) ≫ k)
        (BraidedCategory.braiding_naturality a b)

end AlgebraicGeometry.Etale
