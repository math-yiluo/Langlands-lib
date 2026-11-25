/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapModIhom
import WeilConjectures.CategoryTheory.Monoidal.TensorInverse
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal

/-! # Evaluation for the equalizer dual of a tensor-invertible module -/

@[expose] public section

set_option autoImplicit false

universe v u

namespace CategoryTheory.Mod

open MonoidalCategory Limits MonObj MonoidalClosed

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

private noncomputable def equalizerDualIso (M K : Mod C R) :
    (CategoryTheory.ihom M).obj K ≅ (ihom' R M).obj K :=
  (isLimitIhomToHomMod M K).conePointUniqueUpToIso (limit.isLimit _)

private theorem equalizerDualIso_ι (M K : Mod C R) :
    (equalizerDualIso M K).hom ≫
      equalizer.ι (homModPre (ModObj.smul (M := R) (X := M.X)) K) (homModB R M K) =
      ihomToHomMod M K := by
  exact (isLimitIhomToHomMod M K).conePointUniqueUpToIso_hom_comp
    (limit.isLimit _) WalkingParallelPair.zero

private noncomputable def pairingTranspose {M N K : Mod C R} (b : M ⊗ N ⟶ K) :
    N ⟶ (ihom' R M).obj K :=
  MonoidalClosed.curry b ≫ (equalizerDualIso M K).hom

private theorem pairingTranspose_isIso {M N : Mod C R} (b : M ⊗ N ≅ Mod.regular R) :
    IsIso (pairingTranspose b.hom) := by
  let t : MonoidalCategory.TensorInverse M := ⟨N, b, (β_ N M) ≪≫ b⟩
  let E := t.tensorLeftEquivalence
  have : (MonoidalCategory.tensorLeft M).Full := E.fullyFaithfulFunctor.full
  have : (MonoidalCategory.tensorLeft M).Faithful := E.fullyFaithfulFunctor.faithful
  have : IsIso (MonoidalClosed.curry b.hom) := by
    rw [MonoidalClosed.curry_eq]
    have : IsIso ((CategoryTheory.ihom.coev M).app N) :=
      inferInstanceAs (IsIso ((CategoryTheory.ihom.adjunction M).unit.app N))
    infer_instance
  unfold pairingTranspose
  infer_instance

private theorem pairingTranspose_evaluation {M N K : Mod C R} (b : M ⊗ N ⟶ K) :
    tensorObjπ M N ≫ b.hom =
      M.X ◁ ((pairingTranspose b).hom ≫
        (equalizer.ι (homModPre (ModObj.smul (M := R) (X := M.X)) K)
          (homModB R M K)).hom) ≫ (CategoryTheory.ihom.ev M.X).app K.X := by
  unfold pairingTranspose
  simp only [Mod.comp_hom', Category.assoc]
  rw [← Mod.comp_hom', equalizerDualIso_ι, MonoidalCategory.whiskerLeft_comp_assoc]
  rw [← MonoidalClosed.uncurry_eq, uncurry_ihomToHomMod_hom]
  rw [← tensorObjπ_whiskerLeft_assoc, ← Mod.comp_hom']
  exact congrArg (fun f : M ⊗ N ⟶ K ↦ tensorObjπ M N ≫ f.hom)
    (MonoidalClosed.uncurry_curry b).symm

private theorem pairingTranspose_zero {M N : Mod C R} (b : M ⊗ N ≅ Mod.regular R)
    (eM : M ≅ Mod.regular R) (eN : N ≅ Mod.regular R)
    (hb : b.hom = eM.hom ▷ N ≫ (λ_ N).hom ≫ eN.hom) :
    (pairingTranspose b.hom).hom ≫
      ((λ_ ((ihom' R M).obj (Mod.regular R)).X).inv ≫
        (MonObj.one (X := R) ≫ eM.inv.hom) ▷ ((ihom' R M).obj (Mod.regular R)).X ≫
          M.X ◁ (equalizer.ι
            (homModPre (ModObj.smul (M := R) (X := M.X)) (Mod.regular R))
            (homModB R M (Mod.regular R))).hom ≫ (CategoryTheory.ihom.ev M.X).app R) =
      eN.hom.hom := by
  rw [leftUnitor_inv_naturality_assoc]
  rw [MonoidalCategory.whisker_exchange_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  have hp := pairingTranspose_evaluation b.hom
  change tensorObjπ M N ≫ b.hom.hom = _ ≫ (CategoryTheory.ihom.ev M.X).app R at hp
  rw [← hp]
  rw [hb]
  simp only [Mod.comp_hom']
  rw [tensorObjπ_whiskerRight_assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc]
  have hinv : eM.inv.hom ≫ eM.hom.hom = 𝟙 R :=
    congrArg Mod.Hom.hom eM.inv_hom_id
  simp only [Category.assoc, hinv, Category.comp_id]
  rw [tensorObjπ_regular_leftUnitor_hom_assoc]
  change (λ_ N.X).inv ≫ (MonObj.one (X := R)) ▷ N.X ≫
    ModObj.smul (M := R) (X := N.X) ≫ eN.hom.hom = eN.hom.hom
  have hone : (MonObj.one (X := R)) ▷ N.X ≫ ModObj.smul (M := R) (X := N.X) =
      (λ_ N.X).hom := ModObj.one_smul (M := R) N.X
  rw [reassoc_of% hone]
  simp

/-- A tensor-inverse pairing identifies its second factor with the specified equalizer
internal dual. The identification uses evaluation, and at a trivialized pair it evaluates
functionals on the inverse image of the coefficient unit.
Source: blueprint lemma-artin-schreier-character-sheaf--1, proof steps 7–8.
(blueprint: lem-wft-tensor-inverse-equalizer-dual).
Proof: identify the monoidal internal hom with its equalizer by their universal properties.
The curry of a tensor-inverse pairing is invertible because tensoring with its first factor
is an equivalence. The equation for the equalizer inclusion identifies its underlying
uncurry with the given pairing. Insert the unit followed by the first trivialization's
inverse to obtain the last equation, using the module action's unit law. -/
theorem tensorInverse_equalizerDual {M N : Mod C R} (b : M ⊗ N ≅ Mod.regular R) :
    ∃ δ : (ihom' R M).obj (Mod.regular R) ≅ N,
      (tensorObjπ M N ≫ b.hom.hom =
        M.X ◁ (δ.inv.hom ≫
          (equalizer.ι (homModPre (ModObj.smul (M := R) (X := M.X)) (Mod.regular R))
            (homModB R M (Mod.regular R))).hom) ≫ (CategoryTheory.ihom.ev M.X).app R) ∧
      ∀ (eM : M ≅ Mod.regular R) (eN : N ≅ Mod.regular R),
        b.hom = eM.hom ▷ N ≫ (λ_ N).hom ≫ eN.hom →
        δ.hom.hom ≫ eN.hom.hom =
          (λ_ ((ihom' R M).obj (Mod.regular R)).X).inv ≫
            (MonObj.one (X := R) ≫ eM.inv.hom) ▷ ((ihom' R M).obj (Mod.regular R)).X ≫
              M.X ◁ (equalizer.ι
                (homModPre (ModObj.smul (M := R) (X := M.X)) (Mod.regular R))
                (homModB R M (Mod.regular R))).hom ≫ (CategoryTheory.ihom.ev M.X).app R := by
  have : IsIso (pairingTranspose b.hom) := pairingTranspose_isIso b
  let δ := (asIso (pairingTranspose b.hom)).symm
  refine ⟨δ, pairingTranspose_evaluation b.hom, ?_⟩
  intro eM eN hb
  have : IsIso (pairingTranspose b.hom).hom :=
    inferInstanceAs (IsIso ((forget R).map (pairingTranspose b.hom)))
  rw [← cancel_epi (pairingTranspose b.hom).hom]
  change δ.inv.hom ≫ (δ.hom.hom ≫ eN.hom.hom) = _
  rw [← Category.assoc, ← Mod.comp_hom', δ.inv_hom_id, Mod.id_hom', Category.id_comp]
  exact (pairingTranspose_zero b eM eN hb).symm

end CategoryTheory.Mod
