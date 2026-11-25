/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange

/-! # Tensor interchange for the inverse pullback-square comparison

(blueprint: lem-route-standard-section-pasting-base-change-tensor-interchange).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The inverse pullback-square comparison respects inverse tensor constraints.
Source: composition coherence Step 1, tensor-compositor calculation in Step 6
(blueprint: lem-route-standard-section-pasting-base-change-tensor-interchange).
Proof: the forward pullback-square comparison respects the forward tensor constraints
by the two pullback-composition tensor equations. Express that equality as an equality
of isomorphisms and invert it. Precompose with the tensor constraint for v; its inverse
cancels. This works for every commuting square, including empty schemes.
-/
theorem sectionPullbackTensorInterchange
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {B B' X X' : Scheme.{u}} {v : B' ⟶ B} {s : B ⟶ X} {s' : B' ⟶ X'}
    {r : X' ⟶ X} (sq : CommSq v s' s r)
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    let F := (upperStar A v).leftDerivedFunctor
    let S := (upperStar A s).leftDerivedFunctor
    let S' := (upperStar A s').leftDerivedFunctor
    let R := (upperStar A r).leftDerivedFunctor
    let H := (derivedSquareUpperStarIso A sq).symm
    F.mapIso (leftDerivedUpperStarTensorIso A s K M).symm ≪≫ H.app (K ⊗ M) =
      leftDerivedUpperStarTensorIso A v (S.obj K) (S.obj M) ≪≫
        tensorIso (H.app K) (H.app M) ≪≫
        (leftDerivedUpperStarTensorIso A s' (R.obj K) (R.obj M)).symm ≪≫
        S'.mapIso (leftDerivedUpperStarTensorIso A r K M).symm := by
  dsimp only
  let H := (derivedSquareUpperStarIso A sq).symm
  have hh :
      (upperStar A s').leftDerivedFunctor.mapIso (leftDerivedUpperStarTensorIso A r K M) ≪≫
        leftDerivedUpperStarTensorIso A s' _ _ ≪≫
        tensorIso (H.app K).symm (H.app M).symm =
      (H.app (K ⊗ M)).symm ≪≫
        (upperStar A v).leftDerivedFunctor.mapIso (leftDerivedUpperStarTensorIso A s K M) ≪≫
        leftDerivedUpperStarTensorIso A v _ _ := by
    apply Iso.ext
    exact derivedSquareUpperStarIso_hom_tensor A sq K M
  have hi := congrArg Iso.inv hh
  simp only [Iso.trans_inv, tensorIso_inv, Iso.symm_inv, Functor.mapIso_inv] at hi
  have hp := congrArg (fun z ↦ (leftDerivedUpperStarTensorIso A v
    ((upperStar A s).leftDerivedFunctor.obj K)
    ((upperStar A s).leftDerivedFunctor.obj M)).hom ≫ z) hi
  apply Iso.ext
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, tensorIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc] using hp.symm

end AlgebraicGeometry.Etale
