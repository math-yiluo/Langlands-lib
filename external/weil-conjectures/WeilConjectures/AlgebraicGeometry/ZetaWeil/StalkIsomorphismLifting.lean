/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Lifting continuous maps along a stalkwise isomorphism

Source: Bhatt--Scholze, the more precise statement following Lemma 2.2.8.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem stalk_adjunct {X Y : TopCat.{u}} (f : X ⟶ Y)
    (F : Y.Presheaf CommRingCat.{u}) (G : X.Presheaf CommRingCat.{u})
    (c : F ⟶ (TopCat.Presheaf.pushforward _ f).obj G) (x : X) :
    (TopCat.Presheaf.stalkPullbackIso _ f F x).hom ≫
        (TopCat.Presheaf.stalkFunctor _ x).map
          ((TopCat.Presheaf.pullbackPushforwardAdjunction _ f).homEquiv F G |>.symm c) =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map c ≫ G.stalkPushforward _ f x := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro V hx
  simp only [TopCat.Presheaf.stalkPullbackIso, TopCat.Presheaf.germ_stalkPullbackHom_assoc,
    TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
  have he := congrArg (fun t ↦ t.app (op V))
    (((TopCat.Presheaf.pullbackPushforwardAdjunction _ f).homEquiv F G).apply_symm_apply c)
  change ((TopCat.Presheaf.pullbackPushforwardAdjunction _ f).unit.app F).app (op V) ≫
    ((TopCat.Presheaf.pullbackPushforwardAdjunction _ f).homEquiv F G |>.symm c).app
      (op ((Opens.map f).obj V)) = c.app (op V) at he
  erw [TopCat.Presheaf.stalkFunctor_map_germ, ← Category.assoc, he]

set_option backward.isDefEq.respectTransparency false in
private theorem sheaf_adjunct_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ x : X, IsIso (f.stalkMap x)) :
    IsIso (((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).comp
      (sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat.{u})).homEquiv
      Y.presheaf X.sheaf |>.symm f.c) := by
  let P := (TopCat.Presheaf.pullback CommRingCat.{u} f.base).obj Y.presheaf
  let a : P ⟶ X.presheaf :=
    (TopCat.Presheaf.pullbackPushforwardAdjunction _ f.base).homEquiv _ _ |>.symm f.c
  let b : (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj P ⟶
      X.sheaf :=
    (sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat.{u}).homEquiv
      P X.sheaf |>.symm a
  rw [Adjunction.comp_homEquiv]
  change IsIso b
  have hab : toSheafify (Opens.grothendieckTopology X) P ≫ b.hom = a :=
    (sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat.{u}).homEquiv
      P X.sheaf |>.apply_symm_apply a
  have (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map b.hom) := by
    have ha : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map a) := by
      have he := stalk_adjunct f.base Y.presheaf X.presheaf f.c x
      change (TopCat.Presheaf.stalkPullbackIso _ f.base Y.presheaf x).hom ≫
        (TopCat.Presheaf.stalkFunctor _ x).map a = f.stalkMap x at he
      have := hf x
      have : IsIso ((TopCat.Presheaf.stalkPullbackIso _ f.base Y.presheaf x).hom ≫
          (TopCat.Presheaf.stalkFunctor _ x).map a) := by rw [he]; infer_instance
      exact IsIso.of_isIso_comp_left
        (TopCat.Presheaf.stalkPullbackIso _ f.base Y.presheaf x).hom _
    have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat.{u} P
    have : IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X) P) ≫
          (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map b.hom) := by
      rw [← Functor.map_comp, hab]
      exact ha
    exact IsIso.of_isIso_comp_left
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X) P)) _
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso b

set_option backward.isDefEq.respectTransparency false in
private theorem existsUnique_sheaf_lift {X Y W : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ x : X, IsIso (f.stalkMap x)) (a : W.toTopCat ⟶ X.toTopCat)
    (c : Y.presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat.{u} f.base).obj
        ((TopCat.Presheaf.pushforward CommRingCat.{u} a).obj W.presheaf)) :
    ∃! b : X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} a).obj W.sheaf,
      f.c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} f.base).map b.hom = c := by
  let adj := (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).comp
    (sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat.{u})
  let b₀ := (adj.homEquiv Y.presheaf X.sheaf).symm f.c
  have : IsIso b₀ := sheaf_adjunct_isIso f hf
  let H := (TopCat.Sheaf.pushforward CommRingCat.{u} a).obj W.sheaf
  let d := (adj.homEquiv Y.presheaf H).symm c
  have hb₀ : adj.homEquiv Y.presheaf X.sheaf b₀ = f.c :=
    (adj.homEquiv Y.presheaf X.sheaf).apply_symm_apply f.c
  have hd : adj.homEquiv Y.presheaf H d = c :=
    (adj.homEquiv Y.presheaf H).apply_symm_apply c
  refine ⟨inv b₀ ≫ d, ?_, ?_⟩
  · change f.c ≫ (sheafToPresheaf _ _ ⋙ TopCat.Presheaf.pushforward _ f.base).map (inv b₀ ≫ d) = c
    rw [← hb₀, ← adj.homEquiv_naturality_right, IsIso.hom_inv_id_assoc, hd]
  · intro b hb
    apply (cancel_epi b₀).mp
    apply (adj.homEquiv Y.presheaf H).injective
    rw [adj.homEquiv_naturality_right, hb₀, IsIso.hom_inv_id_assoc, hd]
    exact hb

set_option backward.isDefEq.respectTransparency false in
/-- A continuous lift along a morphism that is an isomorphism on all stalks extends
uniquely to a scheme morphism over the base.

Source: Bhatt--Scholze, the more precise statement following Lemma 2.2.8
(blueprint: new-lem-zl-stalk-isomorphism-lifting).

Proof: transpose the structure-sheaf map along inverse image. On stalks its transpose is
an isomorphism, since inverse image and sheafification preserve stalks; it is therefore
an isomorphism of sheaves. Its inverse gives the unique sheaf map above the specified
continuous map. The composite with the base map is the original structure map by
adjunction. Its stalk maps are the original local maps composed with inverses of local
ring isomorphisms, hence are local. Uniqueness follows from the same adjunction. -/
theorem Scheme.existsUnique_lift_of_stalkMap_isIso {X Y W : Scheme.{u}}
    (f : X ⟶ Y) (hf : ∀ x : X, IsIso (f.stalkMap x)) (g : W ⟶ Y)
    (a : W.toTopCat ⟶ X.toTopCat) (ha : a ≫ f.base = g.base) :
    ∃! m : W ⟶ X, m.base = a ∧ m ≫ f = g := by
  rcases g with ⟨⟨⟨gbase, gc⟩, glocal⟩⟩
  dsimp at ha
  subst gbase
  obtain ⟨b, hb, hbuniq⟩ := existsUnique_sheaf_lift f hf a gc
  let m₀ : W.toPresheafedSpace ⟶ X.toPresheafedSpace := ⟨a, b.hom⟩
  have hcomp : m₀ ≫ f.toLRSHom.toHom =
      (⟨a ≫ f.base, gc⟩ : W.toPresheafedSpace ⟶ Y.toPresheafedSpace) := by
    apply PresheafedSpace.hext
    · rfl
    · exact heq_of_eq hb
  have hlocal (x : W) : IsLocalHom (m₀.stalkMap x).hom := by
    have he : (m₀ ≫ f.toLRSHom.toHom).stalkMap x =
        (⟨a ≫ f.base, gc⟩ : W.toPresheafedSpace ⟶ Y.toPresheafedSpace).stalkMap x := by
      exact congrArg (fun c : Y.presheaf ⟶
          (TopCat.Presheaf.pushforward CommRingCat.{u} (a ≫ f.base)).obj W.presheaf ↦
        (show Y.presheaf.stalk (f.base (a x)) ⟶ W.presheaf.stalk x from
          (⟨a ≫ f.base, c⟩ : W.toPresheafedSpace ⟶ Y.toPresheafedSpace).stalkMap x)) hb
    rw [PresheafedSpace.stalkMap.comp] at he
    change f.stalkMap (a x) ≫ m₀.stalkMap x = _ at he
    have := hf (a x)
    have he' : m₀.stalkMap x = inv (f.stalkMap (a x)) ≫
        (⟨a ≫ f.base, gc⟩ : W.toPresheafedSpace ⟶ Y.toPresheafedSpace).stalkMap x := by
      rw [← he, IsIso.inv_hom_id_assoc]
    rw [he']
    have := glocal x
    infer_instance
  let m : W ⟶ X := ⟨⟨m₀, hlocal⟩⟩
  refine ⟨m, ⟨rfl, ?_⟩, ?_⟩
  · exact Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' hcomp)
  · intro n hn
    rcases n with ⟨⟨⟨nbase, nc⟩, nlocal⟩⟩
    change nbase = a ∧ _ at hn
    obtain ⟨rfl, hn⟩ := hn
    have hnc : f.c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} f.base).map nc =
        gc := by
      have he := congrArg (fun k : W ⟶ Y ↦ k.toLRSHom.toHom) hn
      exact eq_of_heq (PresheafedSpace.Hom.mk.inj he).2
    have hnb := hbuniq (ObjectProperty.homMk nc) hnc
    apply Scheme.Hom.ext'
    apply LocallyRingedSpace.Hom.ext'
    apply PresheafedSpace.hext
    · rfl
    · exact heq_of_eq (congrArg (fun k ↦ k.hom) hnb)

end AlgebraicGeometry
