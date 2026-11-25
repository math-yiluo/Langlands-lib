/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange

/-! # Tensor compatibility of the common-coordinate comparison

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, common coefficient in the second triangle.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

open MonoidalCategory BraidedCategory in
private theorem conjugate_tensor
    {D W : Type*} [Category D] [Category W]
    [MonoidalCategory D] [MonoidalCategory W]
    (R V : D ⥤ W)
    (r : ∀ N Q, R.obj (N ⊗ Q) ≅ R.obj N ⊗ R.obj Q)
    (v : ∀ N Q, V.obj (N ⊗ Q) ≅ V.obj N ⊗ V.obj Q)
    {B L Q T : D} (e : B ≅ L) (d : L ⊗ Q ≅ T)
    (cT : R.obj T ≅ V.obj T) (cL : R.obj L ≅ V.obj L)
    (cQ : R.obj Q ≅ V.obj Q)
    (hc : R.map d.hom ≫ cT.hom ≫ V.map d.inv ≫ (v L Q).hom =
      (r L Q).hom ≫ (cL.hom ⊗ₘ cQ.hom))
    (hr : R.map (e.hom ▷ Q) ≫ (r L Q).hom =
      (r B Q).hom ≫ R.map e.hom ▷ R.obj Q)
    (hv : V.map (e.inv ▷ Q) ≫ (v B Q).hom =
      (v L Q).hom ≫ V.map e.inv ▷ V.obj Q) :
    (R.mapIso (whiskerRightIso e Q ≪≫ d) ≪≫ cT ≪≫
        V.mapIso (whiskerRightIso e Q ≪≫ d).symm).hom ≫ (v B Q).hom =
      (r B Q).hom ≫ ((R.mapIso e ≪≫ cL ≪≫ V.mapIso e.symm).hom ⊗ₘ cQ.hom) := by
  simp only [Iso.trans_hom, Iso.trans_inv, CategoryTheory.Functor.mapIso_hom,
      CategoryTheory.Functor.map_comp,
    Iso.symm_hom, whiskerRightIso_hom, whiskerRightIso_inv, Category.assoc]
  rw [hv, reassoc_of% hc, reassoc_of% hr]
  simp only [MonoidalCategory.tensorHom_def, comp_whiskerRight, Category.assoc]
  rw [whisker_exchange]

namespace AlgebraicGeometry.Etale.SupportedTrace

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  _root_.DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [UpperStarPreservesFlat C]

/-- Split a first-coordinate pullback of a tensor, moving its base coefficient to
its second-coordinate presentation. This is the tensor comparison in the native
exchange/projection square, with no direct image involved.
Source: thm-amb-p1-adjunction.proof.md, extracting the common coefficient
(auxiliary; not a blueprint node). -/
def coefficientSplit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    (upperStar C (pullback.fst f f)).leftDerivedFunctor.obj
        (((derivedTensor C X).obj B).obj ((upperStar C f).leftDerivedFunctor.obj K)) ≅
      ((derivedTensor C (pullback f f)).obj
        ((upperStar C (pullback.fst f f)).leftDerivedFunctor.obj B)).obj
          ((upperStar C (pullback.snd f f)).leftDerivedFunctor.obj
            ((upperStar C f).leftDerivedFunctor.obj K)) :=
  leftDerivedUpperStarTensorIso C (pullback.fst f f) B
      ((upperStar C f).leftDerivedFunctor.obj K) ≪≫
    ((derivedTensor C (pullback f f)).obj
      ((upperStar C (pullback.fst f f)).leftDerivedFunctor.obj B)).mapIso
        ((derivedSquareUpperStarIso C (IsPullback.of_hasPullback f f).toCommSq).app K).symm

/-- The cyclic permutation used when two coefficients are extracted in opposite orders.
Source: thm-amb-p1-adjunction.proof.md, tensor rearrangement in the second triangle
(auxiliary; not a blueprint node). -/
def cyclicShuffle {Z X : Scheme.{u}} (g : Z ⟶ X)
    (E : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C))
    (N Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    ((derivedTensor C Z).obj
      (((derivedTensor C Z).obj E).obj ((upperStar C g).leftDerivedFunctor.obj Q))).obj
        ((upperStar C g).leftDerivedFunctor.obj N) ≅
      ((derivedTensor C Z).obj
        ((upperStar C g).leftDerivedFunctor.obj (((derivedTensor C X).obj N).obj Q))).obj E :=
  derivedTensorAssociator C Z E ((upperStar C g).leftDerivedFunctor.obj Q)
      ((upperStar C g).leftDerivedFunctor.obj N) ≪≫
    ((derivedTensor C Z).obj E).mapIso
      (((derivedTensorSymmetry C Z).app ((upperStar C g).leftDerivedFunctor.obj Q)).app
        ((upperStar C g).leftDerivedFunctor.obj N)) ≪≫
    ((derivedTensor C Z).obj E).mapIso (leftDerivedUpperStarTensorIso C g N Q).symm ≪≫
    (((derivedTensorSymmetry C Z).app E).app
      ((upperStar C g).leftDerivedFunctor.obj (((derivedTensor C X).obj N).obj Q)))

/-- Compare the two coordinate pullbacks by transporting the canonical square comparison.
Source: thm-amb-p1-adjunction.proof.md, common coefficient
(auxiliary; not a blueprint node). -/
def coefficientCoordinate {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C))
    {B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)}
    (e : B ≅ (upperStar C f).leftDerivedFunctor.obj L) :
    (upperStar C (pullback.fst f f)).leftDerivedFunctor.obj B ≅
      (upperStar C (pullback.snd f f)).leftDerivedFunctor.obj B :=
  (upperStar C (pullback.fst f f)).leftDerivedFunctor.mapIso e ≪≫
    (derivedSquareUpperStarIso C (CommSq.mk (pullback.condition (f := f) (g := f)).symm)).app L ≪≫
    (upperStar C (pullback.snd f f)).leftDerivedFunctor.mapIso e.symm

/-- Apply the coordinate comparison to the whole common-base tensor coefficient.
Source: thm-amb-p1-adjunction.proof.md, common coefficient
(auxiliary; not a blueprint node). -/
def tensorCoordinate {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C))
    {B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)}
    (e : B ≅ (upperStar C f).leftDerivedFunctor.obj L) :
    (upperStar C (pullback.fst f f)).leftDerivedFunctor.obj
        (((derivedTensor C X).obj B).obj ((upperStar C f).leftDerivedFunctor.obj K)) ≅
      (upperStar C (pullback.snd f f)).leftDerivedFunctor.obj
        (((derivedTensor C X).obj B).obj ((upperStar C f).leftDerivedFunctor.obj K)) :=
  coefficientCoordinate C f (((derivedTensor C Y).obj L).obj K)
    (((derivedTensor C X).mapIso e).app ((upperStar C f).leftDerivedFunctor.obj K) ≪≫
      (leftDerivedUpperStarTensorIso C f L K).symm)

/-- The coordinate comparison on a common-base tensor is the tensor of the comparisons.
Source: thm-amb-p1-adjunction.proof.md, common coefficient in the second triangle
(auxiliary; not a blueprint node).

Proof: the canonical square comparison is monoidal. Apply its tensor compatibility
on L and K, precompose by the inverse tensor comparison for f*, and cancel its image
under p1*. Conjugate this equality by e tensor the identity and its inverse. Naturality
of the p1* and p2* tensor comparisons transports those maps to e and e inverse on
the first factors. The resulting equation is the stated identity. No self-symmetry,
projection formula or direct image is needed. -/
theorem coordinateTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology C))
    {B : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)}
    (e : B ≅ (upperStar C f).leftDerivedFunctor.obj L) :
    (tensorCoordinate C f L K e).hom ≫
        (leftDerivedUpperStarTensorIso C (pullback.snd f f) B
          ((upperStar C f).leftDerivedFunctor.obj K)).hom =
      (leftDerivedUpperStarTensorIso C (pullback.fst f f) B
        ((upperStar C f).leftDerivedFunctor.obj K)).hom ≫
        ((coefficientCoordinate C f L e).hom ⊗ₘ
          ((derivedSquareUpperStarIso C
            (CommSq.mk (pullback.condition (f := f) (g := f)).symm)).app K).hom) := by
  let U := (upperStar C f).leftDerivedFunctor
  let R := (upperStar C (pullback.fst f f)).leftDerivedFunctor
  let V := (upperStar C (pullback.snd f f)).leftDerivedFunctor
  let r : ∀ N Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C),
      R.obj (N ⊗ Q) ≅ R.obj N ⊗ R.obj Q :=
    leftDerivedUpperStarTensorIso C (pullback.fst f f)
  let v : ∀ N Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C),
      V.obj (N ⊗ Q) ≅ V.obj N ⊗ V.obj Q :=
    leftDerivedUpperStarTensorIso C (pullback.snd f f)
  let c := derivedSquareUpperStarIso C
    (CommSq.mk (pullback.condition (f := f) (g := f)).symm)
  let d : U.obj L ⊗ U.obj K ≅ U.obj (L ⊗ K) :=
    (leftDerivedUpperStarTensorIso C f L K).symm
  let Q := U.obj K
  let cB := coefficientCoordinate C f L e
  let cM := tensorCoordinate C f L K e
  change cM.hom ≫ (v B Q).hom =
    (r B Q).hom ≫ (cB.hom ⊗ₘ c.hom.app K)
  apply conjugate_tensor R V r v e d (c.app _) (c.app L) (c.app K)
  · have h := derivedSquareUpperStarIso_hom_tensor C
      (CommSq.mk (pullback.condition (f := f) (g := f)).symm) L K
    change R.map d.inv ≫ (r (U.obj L) (U.obj K)).hom ≫
        ((c.app L).hom ⊗ₘ (c.app K).hom) =
      (c.app (L ⊗ K)).hom ≫ V.map d.inv ≫
        (v (U.obj L) (U.obj K)).hom at h
    have h' := congrArg (R.map d.hom ≫ ·) h.symm
    rw [← R.map_comp_assoc, d.hom_inv_id,
      R.map_id, Category.id_comp] at h'
    exact h'
  · exact congr_app ((leftDerivedUpperStarTensorComparison C (pullback.fst f f)).naturality
      e.hom) Q
  · exact congr_app ((leftDerivedUpperStarTensorComparison C (pullback.snd f f)).naturality
      e.inv) Q

end AlgebraicGeometry.Etale.SupportedTrace
