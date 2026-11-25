/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Normalization of coefficient comparisons

The categorical coherence argument used for Weil II (1.1.1) d).
(blueprint: new-e5-normalized-fibre-comparisons).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe d
open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

noncomputable section

private lemma liftIsoFromEnd {C D A : Type*} [Category C] [Category D] [Category A]
    (t : C ⥤ D) (F G : D ⥤ A) (a : F ≅ G)
    (h : Function.Bijective (fun u : F ⟶ F ↦ whiskerLeft t u))
    (e : t ⋙ F ≅ t ⋙ G) :
    ∃ u : F ≅ G, Functor.isoWhiskerLeft t u = e := by
  let q := e ≪≫ (Functor.isoWhiskerLeft t a).symm
  obtain ⟨u, hu⟩ := h.surjective q.hom
  obtain ⟨v, hv⟩ := h.surjective q.inv
  dsimp only at hu hv
  have huv : u ≫ v = 𝟙 F := h.injective (by
    change whiskerLeft t u ≫ whiskerLeft t v = 𝟙 _
    rw [hu, hv, q.hom_inv_id])
  have hvu : v ≫ u = 𝟙 F := h.injective (by
    change whiskerLeft t v ≫ whiskerLeft t u = 𝟙 _
    rw [hv, hu, q.inv_hom_id])
  let z : F ≅ F := ⟨u, v, huv, hvu⟩
  refine ⟨z ≪≫ a, ?_⟩
  apply Iso.ext
  change whiskerLeft t u ≫ (Functor.isoWhiskerLeft t a).hom = e.hom
  rw [hu]
  ext X
  simp [q]

private lemma whiskerIsoInjectiveFromEnd {C D A : Type*}
    [Category C] [Category D] [Category A]
    (t : C ⥤ D) (F G : D ⥤ A) (a : F ≅ G)
    (h : Function.Injective (fun u : F ⟶ F ↦ whiskerLeft t u)) :
    Function.Injective (fun u : F ≅ G ↦ Functor.isoWhiskerLeft t u) := by
  intro u v huv
  dsimp only at huv
  have he : u.hom ≫ a.inv = v.hom ≫ a.inv := h (by
    change (Functor.isoWhiskerLeft t u).hom ≫ whiskerLeft t a.inv =
      (Functor.isoWhiskerLeft t v).hom ≫ whiskerLeft t a.inv
    rw [huv])
  apply Iso.ext
  exact (cancel_mono a.inv).mp he

/-- Comparisons of fibres over a preorder with a least object can be normalized when
restriction from that least object is bijective on natural endomorphisms.
Source: the coherence step of Weil II (1.1.1) d), proved here from pseudofunctor axioms.
(blueprint: new-e5-normalized-fibre-comparisons).

Proof: compare all fibres with the least one. Lift the resulting transition comparison
along the bijection on endomorphisms, after dividing by any supplied comparison; lift
its inverse too and use injectivity to prove the inverse identities. Identity and
composition follow after whiskering from the unit and associativity laws of P.
The prescribed restriction from the least object also makes the family unique,
by injectivity of whiskering. -/
theorem Pseudofunctor.normalizedFiberComparisons_exists {B : Type*} [Preorder B]
    (b₀ : B) (hb : ∀ b : B, b₀ ≤ b)
    (P : Pseudofunctor (LocallyDiscrete B) Cat.{d + 1, d + 2})
    {A : Type*} [Category A] (J : ∀ b : B, P.obj ⟨b⟩ ⥤ A)
    (a : ∀ {b c : B} (f : b ⟶ c), J b ≅ (P.map f.toLoc).toFunctor ⋙ J c)
    (h : ∀ b : B, Function.Bijective (fun u : J b ⟶ J b ↦
      whiskerLeft (P.map (homOfLE (hb b)).toLoc).toFunctor u)) :
    ∃! e : ∀ {b c : B} (f : b ⟶ c), J b ≅ (P.map f.toLoc).toFunctor ⋙ J c,
      (∀ (b : B) (X : P.obj ⟨b⟩),
        (e (𝟙 b)).hom.app X ≫ (J b).map ((P.mapId ⟨b⟩).hom.toNatTrans.app X) = 𝟙 _) ∧
      (∀ {b c d : B} (f : b ⟶ c) (g : c ⟶ d) (X : P.obj ⟨b⟩),
        (e (f ≫ g)).hom.app X ≫
            (J d).map ((P.mapComp f.toLoc g.toLoc).hom.toNatTrans.app X) =
          (e f).hom.app X ≫ (e g).hom.app ((P.map f.toLoc).toFunctor.obj X)) ∧
      (∀ {c d : B} (f : c ⟶ d),
        Functor.isoWhiskerLeft (P.map (homOfLE (hb c)).toLoc).toFunctor (e f) =
          (a (homOfLE (hb c))).symm ≪≫ a (homOfLE (hb d)) ≪≫
            Functor.isoWhiskerRight
              (Cat.Hom.toNatIso (P.mapComp (homOfLE (hb c)).toLoc f.toLoc)) (J d) ≪≫
                Functor.associator _ _ _) := by
  let β (b : B) : b₀ ⟶ b := homOfLE (hb b)
  let t (b : B) := (P.map (β b).toLoc).toFunctor
  let b (c : B) := a (β c)
  let z {c d : B} (f : c ⟶ d) : t c ⋙ J c ≅
      t c ⋙ (P.map f.toLoc).toFunctor ⋙ J d :=
    (b c).symm ≪≫ b d ≪≫
      Functor.isoWhiskerRight
        (Cat.Hom.toNatIso (P.mapComp (β c).toLoc f.toLoc)) (J d) ≪≫
          Functor.associator _ _ _
  have he {c d : B} (f : c ⟶ d) :
      ∃ u : J c ≅ (P.map f.toLoc).toFunctor ⋙ J d,
        Functor.isoWhiskerLeft (t c) u = z f :=
    liftIsoFromEnd (t c) _ _ (a f) (h c) (z f)
  choose e hs using @he
  refine ⟨(fun {c d} f ↦ e f), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro c X
    let w : J c ≅ (P.map (𝟙 c).toLoc).toFunctor ⋙ J c :=
      (Functor.leftUnitor (J c)).symm ≪≫
        Functor.isoWhiskerRight (Cat.Hom.toNatIso (P.mapId ⟨c⟩)).symm (J c)
    have hi : e (𝟙 c) = w := by
      apply whiskerIsoInjectiveFromEnd (t c) _ _ (a (𝟙 c)) (h c).injective
      dsimp only
      rw [hs]
      apply Iso.ext
      ext Z
      simp [z, b, w, t, P.mapComp_id_right_hom_app,
        Bicategory.Strict.rightUnitor_eqToIso]
    dsimp only
    rw [hi]
    simp [w, ← Functor.map_comp, ← Cat.Hom₂.comp_app]
  · intro c d q f g X
    dsimp only
    let v : J c ≅ (P.map (f ≫ g).toLoc).toFunctor ⋙ J q :=
      e f ≪≫ Functor.isoWhiskerLeft (P.map f.toLoc).toFunctor (e g) ≪≫
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (Cat.Hom.toNatIso (P.mapComp f.toLoc g.toLoc)).symm (J q)
    have hi : e (f ≫ g) = v := by
      apply whiskerIsoInjectiveFromEnd (t c) _ _ (a (f ≫ g)) (h c).injective
      dsimp only
      rw [hs]
      apply Iso.ext
      ext Z
      have hf := congrArg (fun u ↦ u.hom.app Z) (hs f)
      have hg := congrArg (fun u ↦ u.hom.app Z) (hs g)
      have hfg := (e g).hom.naturality
        ((P.mapComp (β c).toLoc f.toLoc).hom.toNatTrans.app Z)
      dsimp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app] at hf hg
      dsimp only [z, v, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
        Functor.associator_inv_app, Functor.associator_hom_app,
        Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv]
      simp only [Category.id_comp]
      rw [hf]
      simp only [z, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_hom_app,
        Cat.Hom.toNatIso_hom, Category.assoc] at *
      simp only [Functor.comp_obj, Quiver.Hom.comp_toLoc, Cat.Hom.comp_toFunctor,
        Category.comp_id, Category.id_comp, NatIso.cancel_natIso_inv_left] at hf hg ⊢
      change (J d).map ((P.mapComp (β c).toLoc f.toLoc).hom.toNatTrans.app Z) ≫
          (e g).hom.app ((P.map f.toLoc).toFunctor.obj ((t c).obj Z)) =
        (e g).hom.app ((t d).obj Z) ≫ (J q).map
          ((P.map g.toLoc).toFunctor.map
            ((P.mapComp (β c).toLoc f.toLoc).hom.toNatTrans.app Z)) at hfg
      rw [reassoc_of% hfg, hg]
      simp only [Category.assoc]
      simp only [Iso.hom_inv_id_app_assoc]
      congr 1
      rw [← Functor.map_comp, ← Functor.map_comp]
      apply congrArg (J q).map
      have hp := P.mapComp_assoc_right_hom_app (β c).toLoc f.toLoc g.toLoc Z
      have hii : (Bicategory.associator (β c).toLoc f.toLoc g.toLoc).inv =
          𝟙 (((β c).toLoc ≫ f.toLoc) ≫ g.toLoc) := rfl
      rw [hii] at hp
      have hi2 := congrArg (fun u ↦ u.toNatTrans.app Z)
        (P.map₂_id (((β c).toLoc ≫ f.toLoc) ≫ g.toLoc))
      rw [hi2] at hp
      rw [Cat.Hom₂.id_app] at hp
      erw [Category.id_comp] at hp
      have hp' := congrArg (fun k ↦ k ≫
        (P.mapComp f.toLoc g.toLoc).inv.toNatTrans.app ((t c).obj Z)) hp
      have heq : (β c).toLoc ≫ f.toLoc = (β d).toLoc := rfl
      rw [heq] at hp'
      with_unfolding_all
        simpa [t, Category.assoc, ← Cat.Hom₂.comp_app,
          Cat.Hom.comp_toFunctor, Functor.comp_obj, Quiver.Hom.comp_toLoc] using hp'
    rw [hi]
    simp [v, Category.assoc, ← Functor.map_comp]
  · exact fun {_ _} f ↦ hs f
  · intro e' he'
    funext c d f
    apply whiskerIsoInjectiveFromEnd (t c) _ _ (a f) (h c).injective
    exact (he'.2.2 f).trans (hs f).symm

/-- The unique comparison family normalized against the prescribed comparisons from
its least coefficient field. Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-normalized-fibre-comparisons). -/
@[irreducible]
def Pseudofunctor.normalizedFiberComparisons {B : Type*} [Preorder B]
    (b₀ : B) (hb : ∀ b : B, b₀ ≤ b)
    (P : Pseudofunctor (LocallyDiscrete B) Cat.{d + 1, d + 2})
    {A : Type*} [Category A] (J : ∀ b : B, P.obj ⟨b⟩ ⥤ A)
    (a : ∀ {b c : B} (f : b ⟶ c), J b ≅ (P.map f.toLoc).toFunctor ⋙ J c)
    (h : ∀ b : B, Function.Bijective (fun u : J b ⟶ J b ↦
      whiskerLeft (P.map (homOfLE (hb b)).toLoc).toFunctor u)) :
    ∀ {b c : B} (f : b ⟶ c), J b ≅ (P.map f.toLoc).toFunctor ⋙ J c :=
  (Pseudofunctor.normalizedFiberComparisons_exists b₀ hb P J a h).exists.choose

/-- The normalization and coherence of the selected, unique comparison family.
Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-normalized-fibre-comparisons).
Proof: apply the specification of the uniquely determined comparison family. -/
theorem Pseudofunctor.normalizedFiberComparisons_spec {B : Type*} [Preorder B]
    (b₀ : B) (hb : ∀ b : B, b₀ ≤ b)
    (P : Pseudofunctor (LocallyDiscrete B) Cat.{d + 1, d + 2})
    {A : Type*} [Category A] (J : ∀ b : B, P.obj ⟨b⟩ ⥤ A)
    (a : ∀ {b c : B} (f : b ⟶ c), J b ≅ (P.map f.toLoc).toFunctor ⋙ J c)
    (h : ∀ b : B, Function.Bijective (fun u : J b ⟶ J b ↦
      whiskerLeft (P.map (homOfLE (hb b)).toLoc).toFunctor u)) :
    let e := @Pseudofunctor.normalizedFiberComparisons B _ b₀ hb P A _ J a h;
      (∀ (b : B) (X : P.obj ⟨b⟩),
        (e (𝟙 b)).hom.app X ≫ (J b).map ((P.mapId ⟨b⟩).hom.toNatTrans.app X) = 𝟙 _) ∧
      (∀ {b c d : B} (f : b ⟶ c) (g : c ⟶ d) (X : P.obj ⟨b⟩),
        (e (f ≫ g)).hom.app X ≫
            (J d).map ((P.mapComp f.toLoc g.toLoc).hom.toNatTrans.app X) =
          (e f).hom.app X ≫ (e g).hom.app ((P.map f.toLoc).toFunctor.obj X)) ∧
      (∀ {c d : B} (f : c ⟶ d),
        Functor.isoWhiskerLeft (P.map (homOfLE (hb c)).toLoc).toFunctor (e f) =
          (a (homOfLE (hb c))).symm ≪≫ a (homOfLE (hb d)) ≪≫
            Functor.isoWhiskerRight
              (Cat.Hom.toNatIso (P.mapComp (homOfLE (hb c)).toLoc f.toLoc)) (J d) ≪≫
                Functor.associator _ _ _) := by
  unfold Pseudofunctor.normalizedFiberComparisons
  exact (Pseudofunctor.normalizedFiberComparisons_exists b₀ hb P J a h).exists.choose_spec

/-- The functor on coefficient pairs constructed from the uniquely normalized comparisons.
Source: Weil II (1.1.1) d), pp.146-147.
(blueprint: new-e5-normalized-fibre-comparisons). -/
@[irreducible]
def Pseudofunctor.normalizedGrothendieckFiberFunctor {B : Type*} [Preorder B]
    (b₀ : B) (hb : ∀ b : B, b₀ ≤ b)
    (P : Pseudofunctor (LocallyDiscrete B) Cat.{d + 1, d + 2})
    {A : Type*} [Category A] (J : ∀ b : B, P.obj ⟨b⟩ ⥤ A)
    (a : ∀ {b c : B} (f : b ⟶ c), J b ≅ (P.map f.toLoc).toFunctor ⋙ J c)
    (h : ∀ b : B, Function.Bijective (fun u : J b ⟶ J b ↦
      whiskerLeft (P.map (homOfLE (hb b)).toLoc).toFunctor u)) :
    Pseudofunctor.Grothendieck P ⥤ A :=
  let e := @Pseudofunctor.normalizedFiberComparisons B _ b₀ hb P A _ J a h
  let he := Pseudofunctor.normalizedFiberComparisons_spec b₀ hb P J a h
  { obj X := (J X.base).obj X.fiber
    map {X Y} f := (e f.base).hom.app X.fiber ≫ (J Y.base).map f.fiber
    map_id X := he.1 X.base X.fiber
    map_comp {X Y Z} f g := by
      simp only [Pseudofunctor.Grothendieck.categoryStruct_comp_base,
        Pseudofunctor.Grothendieck.categoryStruct_comp_fiber]
      rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, he.2.1]
      simp only [Category.assoc]
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun k ↦ (e f.base).hom.app X.fiber ≫ k ≫ (J Z.base).map g.fiber)
          ((e g.base).hom.naturality f.fiber).symm }

end

end CategoryTheory
