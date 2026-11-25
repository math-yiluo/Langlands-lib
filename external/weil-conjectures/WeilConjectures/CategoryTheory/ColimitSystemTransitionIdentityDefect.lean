/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Transitions on an augmented product of direct images

Source: Stacks Project, Sites, Lemma 0EXZ, product and transition construction.
(blueprint: lem-weil-pbc-transition-identity-defect)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0EXZ, transition cocycle; nonunital
identity correction written by X3 in the parent node, step 3.
(blueprint: lem-weil-pbc-transition-identity-defect)

Proof in words: set e_k=φ_id followed by the identity comparison E_k.
The cocycle for a and id_k, together with a≫id_k=a and the coherence of the
identity and composition comparisons, says φ_a R_a(e_k)=φ_a. Since pushforward
is additive, φ_a R_a(1-e_k)=φ_a-φ_a=0. Postcomposing with R_a(ι_k) proves
this assertion. The argument also covers zero identity transitions and empty J. -/
theorem colimitSystem_transition_identity_defect
    {J : Type u} [SmallCategory J]
    (F : J ⥤ Cat.{u, u}) (T : ∀ j : J, GrothendieckTopology (F.obj j))
    [∀ (j k : J) (a : j ⟶ k), (F.map a).toFunctor.IsContinuous (T j) (T k)]
    (Fs : ∀ j : J, Sheaf (T j) AddCommGrpCat.{u})
    (φ : ∀ {j k : J} (a : j ⟶ k),
      Fs j ⟶ ((F.map a).toFunctor.sheafPushforwardContinuous
        AddCommGrpCat.{u} (T j) (T k)).obj (Fs k))
    (hφ : ∀ {j k l : J} (a : j ⟶ k) (b : k ⟶ l),
      φ (a ≫ b) = φ a ≫
        ((F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u}
          (T j) (T k)).map (φ b) ≫
        (Functor.sheafPushforwardContinuousComp'
          (eqToIso (congrArg Cat.Hom.toFunctor (F.map_comp a b).symm))
          AddCommGrpCat.{u} (T j) (T k) (T l)).hom.app (Fs l))
    (A : ∀ j : J, Sheaf (T j) AddCommGrpCat.{u}) (ι : ∀ j, Fs j ⟶ A j) :
    let R := fun {j k : J} (a : j ⟶ k) ↦
      (F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (T j) (T k)
    let E := fun j ↦ Functor.sheafPushforwardContinuousId'
      (eqToIso (congrArg Cat.Hom.toFunctor (F.map_id j))) AddCommGrpCat.{u} (T j)
    ∀ {j k : J} (a : j ⟶ k),
      φ a ≫ (R a).map
        ((𝟙 (Fs k) - (φ (𝟙 k) ≫ (E k).hom.app (Fs k) : Fs k ⟶ Fs k)) ≫ ι k) =
          0 := by
  dsimp
  intro j k a
  have hc : (F.map a).toFunctor ⋙ (F.map (𝟙 k)).toFunctor =
      (F.map a).toFunctor := by
    simpa only [Cat.Hom.comp_toFunctor, Category.comp_id] using
      congrArg Cat.Hom.toFunctor (F.map_comp a (𝟙 k)).symm
  have hh : φ a = φ a ≫
      ((F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (T j) (T k)).map
        (φ (𝟙 k)) ≫
      (Functor.sheafPushforwardContinuousComp' (eqToIso hc)
        AddCommGrpCat.{u} (T j) (T k) (T k)).hom.app (Fs k) := by
    convert hφ a (𝟙 k) using 1
    · simp only [Category.comp_id]
    · exact (congr_arg_heq (fun b : j ⟶ k ↦ φ b) (Category.comp_id a)).symm
    · congr! 6
      all_goals simp only [Category.comp_id]
  have he :
      (Functor.sheafPushforwardContinuousComp' (eqToIso hc)
        AddCommGrpCat.{u} (T j) (T k) (T k)).hom.app (Fs k) =
      ((F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (T j) (T k)).map
        ((Functor.sheafPushforwardContinuousId'
          (eqToIso (congrArg Cat.Hom.toFunctor (F.map_id k)))
          AddCommGrpCat.{u} (T k)).hom.app (Fs k)) := by
    apply Sheaf.hom_ext
    ext X
    simp only [Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
      Functor.sheafPushforwardContinuous_map_hom_app,
      Functor.sheafPushforwardContinuousId'_hom_app_hom_app]
    congr 3
    simp only [eqToIso.inv, eqToHom_app]
  have hfix : φ a ≫
      ((F.map a).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} (T j) (T k)).map
        (φ (𝟙 k) ≫
          (Functor.sheafPushforwardContinuousId'
            (eqToIso (congrArg Cat.Hom.toFunctor (F.map_id k)))
            AddCommGrpCat.{u} (T k)).hom.app (Fs k)) = φ a := by
    simpa only [Functor.map_comp, he] using hh.symm
  have : ((F.map a).toFunctor.sheafPushforwardContinuous
      AddCommGrpCat.{u} (T j) (T k)).Additive := by
    dsimp only [Functor.sheafPushforwardContinuous]
    infer_instance
  rw [Functor.map_comp, ← Category.assoc, Functor.map_sub, Preadditive.comp_sub,
    Functor.map_id, Category.comp_id, hfix, sub_self, zero_comp]

end CategoryTheory
