/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Evaluation-defined tensor-Hom comparison for invertible factors -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- Tensor-Hom comparison is invertible when its line factors are invertible.
Source: the closed symmetric monoidal argument underlying Bhatt--Scholze 6.8.14.
Proof: write H=Hom(K,L), G=Hom(P,Q). Evaluation for invertible P identifies
P tensor (H tensor G) with H tensor Q. The canonical map H tensor Q to
Hom(K,L tensor Q) is invertible because Q is invertible. Curry in P; the
unit of this adjunction is invertible because tensoring with P is an equivalence.
Double uncurrying and monoidal coherence identify this composite with the given
two-evaluation transpose followed by the internal currying isomorphism. Cancel
the latter. No dualizability of K or L is needed.
(blueprint: lem-per-invertible-factor-tensor-hom). -/
theorem tensorHom_isIso_of_isInvertible
    {C : Type*} [Category* C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] (K L P Q : C) (hP : IsInvertible P) (hQ : IsInvertible Q) :
    IsIso (MonoidalClosed.curry
      (tensorμ K P ((ihom K).obj L) ((ihom P).obj Q) ≫
        ((ihom.ev K).app L ⊗ₘ (ihom.ev P).app Q))) := by
  let H := (ihom K).obj L
  let G := (ihom P).obj Q
  have := hP.isIso_ev Q
  let g : P ⊗ (H ⊗ G) ≅ H ⊗ Q :=
    (α_ P H G).symm ≪≫ tensorIso (β_ P H) (Iso.refl G) ≪≫
      α_ H P G ≪≫ whiskerLeftIso H (asIso ((ihom.ev P).app Q))
  have := MonoidalClosed.isIso_ihomTensorToIhom K L hQ
  have := hP.isEquivalence_tensorLeft
  have hu : IsIso ((ihom.adjunction P).unit.app (H ⊗ G)) :=
    NatTrans.isIso_iff_isIso_app _ |>.mp
      (Adjunction.unit_isIso_of_L_fully_faithful (ihom.adjunction P)) _
  have : IsIso ((ihom.coev P).app (H ⊗ G)) := hu
  have hf : IsIso (MonoidalClosed.curry
      (g.hom ≫ MonoidalClosed.ihomTensorToIhom K L Q)) := by
    rw [MonoidalClosed.curry_eq]
    infer_instance
  have he : MonoidalClosed.curry
      (tensorμ K P H G ≫ ((ihom.ev K).app L ⊗ₘ (ihom.ev P).app Q)) ≫
      (MonoidalClosed.ihomCurryIso K P (L ⊗ Q)).hom =
        MonoidalClosed.curry (g.hom ≫ MonoidalClosed.ihomTensorToIhom K L Q) := by
    simp only [MonoidalClosed.ihomCurryIso_hom]
    apply MonoidalClosed.uncurry_injective
    apply MonoidalClosed.uncurry_injective
    simp only [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
      MonoidalClosed.uncurry_uncurry_ihomCurry, Functor.id_obj]
    rw [← Category.assoc, associator_inv_naturality_right, Category.assoc,
      ← MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_curry]
    simp only [MonoidalClosed.ihomTensorToIhom, MonoidalClosed.uncurry_curry,
      g, tensorμ, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
      whiskerLeftIso_hom, asIso_hom, whiskerLeft_comp, tensorHom_id,
      Functor.id_obj, Category.assoc]
    simp only [Iso.inv_hom_id_assoc]
    dsimp only [H, G]
    rw [dsimp% associator_inv_naturality_right_assoc K ((ihom K).obj L) ((ihom.ev P).app Q)]
    rw [← dsimp% MonoidalCategory.tensorHom_def' ((ihom.ev K).app L) ((ihom.ev P).app Q)]
  have : IsIso (MonoidalClosed.curry
      (tensorμ K P H G ≫ ((ihom.ev K).app L ⊗ₘ (ihom.ev P).app Q)) ≫
        (MonoidalClosed.ihomCurryIso K P (L ⊗ Q)).hom) := by
    rw [he]
    exact hf
  exact IsIso.of_isIso_comp_right _ (MonoidalClosed.ihomCurryIso K P (L ⊗ Q)).hom

end CategoryTheory
