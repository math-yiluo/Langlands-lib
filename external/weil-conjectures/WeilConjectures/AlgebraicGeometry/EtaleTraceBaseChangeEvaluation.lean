/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceData
import WeilConjectures.AlgebraicGeometry.EtaleOrderedProjectionComparison

/-! # Base change of a trace evaluation

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, second triangle.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.CoordinateTrace

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

section General
open MonoidalCategory
variable (B : Type*) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]

private abbrev coeffObjects (X : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)

private abbrev coeffPull {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar B f).leftDerivedFunctor

private abbrev coeffPush {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (lowerStar B f).rightDerivedFunctor

omit [UpperStarPreservesFlat B] in
private theorem compositor_congr
    {Z X X' Y : Scheme.{u}} (a : Z ⟶ X) (b : X ⟶ Y)
    (a' : Z ⟶ X') (b' : X' ⟶ Y) (c1 c2 : Z ⟶ Y)
    (h1 : c1 = a ≫ b) (h1' : c1 = a' ≫ b')
    (h2 : c2 = a ≫ b) (h2' : c2 = a' ≫ b') (K : (coeffObjects B Y)) :
    (leftDerivedUpperStarComp B a b c1 h1).inv.app K ≫
        (leftDerivedUpperStarComp B a' b' c1 h1').hom.app K =
      (leftDerivedUpperStarComp B a b c2 h2).inv.app K ≫
        (leftDerivedUpperStarComp B a' b' c2 h2').hom.app K := by
  obtain rfl : c1 = c2 := h1.trans h2.symm
  rfl

omit [UpperStarPreservesFlat B] in
private theorem reverse_square {X Y : Scheme.{u}} (f : X ⟶ Y) (K : (coeffObjects B Y)) :
    (derivedSquareUpperStarIso B (IsPullback.of_hasPullback f f).toCommSq).inv.app K =
      (derivedSquareUpperStarIso B
        (CommSq.mk (pullback.condition (f := f) (g := f)).symm)).hom.app K := by
  exact compositor_congr B (pullback.fst f f) f (pullback.snd f f) f _ _
    rfl (pullback.condition (f := f) (g := f))
    (pullback.condition (f := f) (g := f)).symm rfl K

private theorem coordinate_tensor {X Y : Scheme.{u}} (f : X ⟶ Y) (K L : (coeffObjects B Y)) :
    ((leftDerivedUpperStarTensorComparison B (pullback.fst f f)).app
        ((coeffPull B f).obj K)).app ((coeffPull B f).obj L) ≫
      derivedTensorHom B
        ((derivedSquareUpperStarIso B (IsPullback.of_hasPullback f f).toCommSq).inv.app K)
        ((derivedSquareUpperStarIso B
          (CommSq.mk (pullback.condition (f := f) (g := f)).symm)).hom.app L) =
      (coeffPull B (pullback.fst f f)).map (leftDerivedUpperStarTensorIso B f K L).inv ≫
        (derivedSquareUpperStarIso B
          (CommSq.mk (pullback.condition (f := f) (g := f)).symm)).hom.app
            (((derivedTensor B Y).obj K).obj L) ≫
        (coeffPull B (pullback.snd f f)).map (leftDerivedUpperStarTensorIso B f K L).hom ≫
        (leftDerivedUpperStarTensorIso B (pullback.snd f f)
          ((coeffPull B f).obj K) ((coeffPull B f).obj L)).hom := by
  rw [reverse_square]
  let R := (coeffPull B (pullback.fst f f))
  let V := (coeffPull B (pullback.snd f f))
  let d := leftDerivedUpperStarTensorIso B f K L
  have h := derivedSquareUpperStarIso_hom_tensor B
    (CommSq.mk (pullback.condition (f := f) (g := f)).symm) K L
  change R.map d.hom ≫ _ = _ at h
  have h' := congrArg (R.map d.inv ≫ ·) h
  rw [← R.map_comp_assoc, d.inv_hom_id, R.map_id, Category.id_comp] at h'
  exact h'

private theorem evaluation_general {X Y : Scheme.{u}} (f : X ⟶ Y) (L K : (coeffObjects B Y))
    (c : (coeffPull B (pullback.fst f f)).obj ((coeffPull B f).obj L) ≅
      (coeffPull B (pullback.snd f f)).obj ((coeffPull B f).obj L))
    (cH : (coeffPull B (pullback.fst f f)).obj (((derivedTensor B X).obj ((coeffPull B f).obj
      K)).obj ((coeffPull B f).obj L)) ≅
      (coeffPull B (pullback.snd f f)).obj (((derivedTensor B X).obj ((coeffPull B f).obj K)).obj
        ((coeffPull B f).obj L)))
    (q : ((derivedTensor B Y).obj K).obj ((coeffPush B f).obj ((coeffPull B f).obj L)) ≅
      (coeffPush B f).obj (((derivedTensor B X).obj ((coeffPull B f).obj K)).obj ((coeffPull B
        f).obj L)))
    (q' : ((derivedTensor B X).obj ((coeffPull B f).obj K)).obj
        ((coeffPush B (pullback.snd f f)).obj ((coeffPull B (pullback.snd f f)).obj ((coeffPull B
          f).obj L))) ≅
      (coeffPush B (pullback.snd f f)).obj (((derivedTensor B (pullback f f)).obj
        ((coeffPull B (pullback.snd f f)).obj ((coeffPull B f).obj K))).obj
          ((coeffPull B (pullback.snd f f)).obj ((coeffPull B f).obj L))))
    (t : (coeffPush B f).obj ((coeffPull B f).obj L) ⟶ 𝟙_ (coeffObjects B Y))
    (t2 : (coeffPush B (pullback.snd f f)).obj
      ((coeffPull B (pullback.snd f f)).obj ((coeffPull B f).obj L)) ⟶ 𝟙_ (coeffObjects B X))
    (ht : (derivedBaseChangeMap B (IsPullback.of_hasPullback f f).toCommSq).app
        ((coeffPull B f).obj L) ≫ (coeffPush B (pullback.snd f f)).map c.hom ≫ t2 =
      (coeffPull B f).map t ≫ (leftDerivedUpperStarUnitIso B f).hom)
    (hq : q.hom = ((derivedTensorSymmetry B Y).app K).hom.app
        ((coeffPush B f).obj ((coeffPull B f).obj L)) ≫
      ((rightDerivedLowerStarProjectionMap B f).app ((coeffPull B f).obj L)).app K ≫
      (coeffPush B f).map (((derivedTensorSymmetry B X).app ((coeffPull B f).obj L)).hom.app
        ((coeffPull B f).obj K)))
    (hq' : q'.hom = ((derivedTensorSymmetry B X).app ((coeffPull B f).obj K)).hom.app
        ((coeffPush B (pullback.snd f f)).obj ((coeffPull B (pullback.snd f f)).obj ((coeffPull B
          f).obj L))) ≫
      ((rightDerivedLowerStarProjectionMap B (pullback.snd f f)).app
        ((coeffPull B (pullback.snd f f)).obj ((coeffPull B f).obj L))).app ((coeffPull B f).obj
          K) ≫
      (coeffPush B (pullback.snd f f)).map (((derivedTensorSymmetry B (pullback f f)).app
        ((coeffPull B (pullback.snd f f)).obj ((coeffPull B f).obj L))).hom.app
          ((coeffPull B (pullback.snd f f)).obj ((coeffPull B f).obj K))))
    (hc : ((leftDerivedUpperStarTensorComparison B (pullback.fst f f)).app
        ((coeffPull B f).obj K)).app ((coeffPull B f).obj L) ≫
      derivedTensorHom B
        ((derivedSquareUpperStarIso B (IsPullback.of_hasPullback f f).toCommSq).inv.app K)
        c.hom = cH.hom ≫
      (leftDerivedUpperStarTensorIso B (pullback.snd f f) ((coeffPull B f).obj K) ((coeffPull B
        f).obj L)).hom) :
    (coeffPull B f).map (q.inv ≫ ((derivedTensor B Y).obj K).map t ≫ (derivedTensorRightUnitor B Y
      K).hom) =
      (derivedBaseChangeMap B (IsPullback.of_hasPullback f f).toCommSq).app
        (((derivedTensor B X).obj ((coeffPull B f).obj K)).obj ((coeffPull B f).obj L)) ≫
      (coeffPush B (pullback.snd f f)).map cH.hom ≫
      (coeffPush B (pullback.snd f f)).map
        (leftDerivedUpperStarTensorIso B (pullback.snd f f) ((coeffPull B f).obj K) ((coeffPull B
          f).obj L)).hom ≫
      q'.inv ≫ ((derivedTensor B X).obj ((coeffPull B f).obj K)).map t2 ≫
        (derivedTensorRightUnitor B X ((coeffPull B f).obj K)).hom := by
  have hu : ((canonicalPullbackTensorComparison B f).app K).app (𝟙_ (coeffObjects B Y)) ≫
      ((derivedTensor B X).obj ((coeffPull B f).obj K)).map (leftDerivedUpperStarUnitIso B f).hom ≫
        (derivedTensorRightUnitor B X ((coeffPull B f).obj K)).hom =
      (coeffPull B f).map (derivedTensorRightUnitor B Y K).hom := by
    rw [canonicalPullbackTensorComparison_eq]
    exact leftDerivedUpperStarTensorComparison_rightUnitor_hom B f K
  have h := etaleTensorEvaluation_constant_baseChange B
    (IsPullback.of_hasPullback f f).toCommSq ((coeffPull B f).obj L)
    ((coeffPull B (pullback.snd f f)).obj ((coeffPull B f).obj L)) c (𝟙_ (coeffObjects B Y)) (𝟙_
      (coeffObjects B X))
    (leftDerivedUpperStarUnitIso B f).hom
    (derivedTensorRightUnitor B Y) (derivedTensorRightUnitor B X)
    t t2 ht.symm K hu q.hom q'.hom
    (hq.trans (orderedProjection_eq_symmetry B f ((coeffPull B f).obj L) K).symm)
    (hq'.trans (orderedProjection_eq_symmetry B (pullback.snd f f)
      ((coeffPull B (pullback.snd f f)).obj ((coeffPull B f).obj L)) ((coeffPull B f).obj K)).symm)
  rw [show inv q.hom = q.inv from IsIso.inv_eq_of_hom_inv_id q.hom_inv_id,
    show inv q'.hom = q'.inv from IsIso.inv_eq_of_hom_inv_id q'.hom_inv_id] at h
  rw [canonicalPullbackTensorComparison_app_eq, hc, (coeffPush B (pullback.snd f f)).map_comp] at h
  simpa only [Category.assoc] using h

end General

variable (A : Type (u + 1)) [CommRing A]

/-- Base change identifies evaluation with integration in the second projection.
Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, second triangle; Stacks 0E48 and 0B56.
(auxiliary; not a blueprint node).

Proof: apply the canonical projection/exchange square to f and its self pullback,
with the kernel f*L and coefficient K. Conjugate by the tensor symmetries to order
K first and invert the projection and exchange isomorphisms. Naturality of the
pullback tensor comparison moves f*t to the kernel factor. The trace compatibility
hypothesis replaces exchange followed by coordinate and t2 with f*t followed by the
unit comparison. Pullback preserves the right unitor with precisely that unit
comparison. The tensor compatibility of the square comparison identifies its
component on K tensor L with coordinateH followed by the p2 tensor comparison.
Cancel the inverse unit and tensor comparisons. This yields the displayed formula.
No self symmetry hypothesis, exterior tensor factor, or diagonal class is used. -/
theorem traceBaseChangeEvaluation [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (L : DerivedCategoryModule A Y)
    (t : (push A f).obj ((pull A f).obj L) ⟶ constantComplex A Y)
    (t2 : (push A (pullback.snd f f)).obj
        ((pull A (pullback.snd f f)).obj ((pull A f).obj L)) ⟶ constantComplex A X)
    (ht : (exchange2 A f ((pull A f).obj L)).hom ≫
        (push A (pullback.snd f f)).map (coordinate A f L).hom ≫ t2 =
      (pull A f).map t ≫ (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom)
    (K : DerivedCategoryModule A Y) :
    (exchange2 A f ((H A f L).obj K)).inv ≫
        (pull A f).map (evaluation A f L t K) =
      (push A (pullback.snd f f)).map (coordinateH A f L K).hom ≫
        (push A (pullback.snd f f)).map
          (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) (pullback.snd f f)
            ((pull A f).obj K) ((pull A f).obj L)).hom ≫
        (orderedProjectionIso A (pullback.snd f f) ((pull A f).obj K)
          ((pull A (pullback.snd f f)).obj ((pull A f).obj L))).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj ((pull A f).obj K)).map t2 ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} A) X ((pull A f).obj K)).hom := by
  have hc := coordinate_tensor (ModuleCat.{u + 1} A) f K L
  have h := evaluation_general (ModuleCat.{u + 1} A) f L K
    (coordinate A f L) (coordinateH A f L K)
    (orderedProjectionIso A f K ((pull A f).obj L))
    (orderedProjectionIso A (pullback.snd f f) ((pull A f).obj K)
      ((pull A (pullback.snd f f)).obj ((pull A f).obj L)))
    t t2 ht rfl rfl (by
      simpa only [coordinateH, coordinate, tensor, H, derivedTensorRight,
        Functor.comp_obj, Functor.flip_obj_obj, Iso.trans_hom, Functor.mapIso_hom,
        Iso.symm_hom, Iso.app_hom, coeffPull, pull, Category.assoc] using hc)
  apply (cancel_epi (exchange2 A f ((H A f L).obj K)).hom).1
  rw [Iso.hom_inv_id_assoc]
  simpa only [exchange2, asIso_hom, H, derivedTensorRight,
    Functor.comp_obj, Functor.flip_obj_obj, evaluation] using h

end AlgebraicGeometry.Etale.CoordinateTrace
