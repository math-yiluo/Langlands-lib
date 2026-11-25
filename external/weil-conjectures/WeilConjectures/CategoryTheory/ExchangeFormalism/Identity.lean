/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.Coherence
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Identity squares in an exchange formalism

In a `CategoryTheory.ExchangeFormalism`, the base change and exchange maps of the
squares with two identity sides are the identity isomorphisms `(𝟙 X)^* ≅ 𝟭`, `(𝟙 X)_* ≅ 𝟭` and
`(𝟙 X)_! ≅ 𝟭`, and the composition isomorphisms with an identity are the unitors.
-/

@[expose] public section

universe w v₁ v u

namespace CategoryTheory.ExchangeFormalism

open TwoSquare

variable {𝒞 : Type u} [Category.{v} 𝒞] {𝒪 : MorphismProperty 𝒞}
  (F : ExchangeFormalism.{w, v₁} 𝒞 𝒪)

section Unit

variable {X Y : 𝒞}

lemma pbComp'_id_left_hom (f : X ⟶ Y) :
    (F.pbComp' (𝟙 X) f f (Category.id_comp f)).hom ≫
        Functor.whiskerLeft (F.pb f) (F.pbId X).hom ≫ (Functor.rightUnitor (F.pb f)).hom =
      𝟙 _ := by
  ext M
  simpa using F.pbComp'_id_left f f (Category.id_comp f) M

lemma pbComp'_id_right_hom (f : X ⟶ Y) :
    (F.pbComp' f (𝟙 Y) f (Category.comp_id f)).hom ≫
        Functor.whiskerRight (F.pbId Y).hom (F.pb f) ≫ (Functor.leftUnitor (F.pb f)).hom =
      𝟙 _ := by
  ext M
  simpa using F.pbComp'_id_right f f (Category.comp_id f) M

/-- The comparison isomorphism of a commutative square through a common diagonal `d`. -/
lemma sqIso_eq {U' U Z' Z : 𝒞} (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z)
    (w : t ≫ r = l ≫ b) (d : U' ⟶ Z) (hd₁ : t ≫ r = d) (hd₂ : l ≫ b = d) :
    F.sqIso t l r b w = (F.pbComp' t r d hd₁).symm ≪≫ F.pbComp' l b d hd₂ := by
  subst hd₁
  rfl

/-- The inverse of the square isomorphism of a square is the square isomorphism of the transposed
square. -/
lemma sqIso_symm {U' U Z' Z : 𝒞} (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z)
    (w : t ≫ r = l ≫ b) : (F.sqIso t l r b w).symm = F.sqIso l t b r w.symm := by
  rw [F.sqIso_eq l t b r w.symm (t ≫ r) w.symm rfl]
  rfl

lemma pbComp'_id_left_inv_app (f : X ⟶ Y) (M : F.obj Y) :
    (F.pbComp' (𝟙 X) f f (Category.id_comp f)).inv.app M = (F.pbId X).hom.app _ := by
  rw [← cancel_epi ((F.pbComp' (𝟙 X) f f (Category.id_comp f)).hom.app M), Iso.hom_inv_id_app]
  simpa using (congr_app (F.pbComp'_id_left_hom f) M).symm

lemma pbComp'_id_right_hom_app (f : X ⟶ Y) (M : F.obj Y) :
    (F.pbComp' f (𝟙 Y) f (Category.comp_id f)).hom.app M =
      (F.pb f).map ((F.pbId Y).inv.app M) := by
  rw [← cancel_mono ((F.pb f).map ((F.pbId Y).hom.app M)), ← Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simpa using congr_app (F.pbComp'_id_right_hom f) M

lemma pbComp'_id_left_hom_app (f : X ⟶ Y) (M : F.obj Y) :
    (F.pbComp' (𝟙 X) f f (Category.id_comp f)).hom.app M = (F.pbId X).inv.app _ := by
  rw [← cancel_mono ((F.pbId X).hom.app _), Iso.inv_hom_id_app]
  simpa using congr_app (F.pbComp'_id_left_hom f) M

lemma pbComp'_id_right_inv_app (f : X ⟶ Y) (M : F.obj Y) :
    (F.pbComp' f (𝟙 Y) f (Category.comp_id f)).inv.app M =
      (F.pb f).map ((F.pbId Y).hom.app M) := by
  rw [← cancel_epi ((F.pbComp' f (𝟙 Y) f (Category.comp_id f)).hom.app M), Iso.hom_inv_id_app,
    pbComp'_id_right_hom_app, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  rfl

/-- The square isomorphism of the square `𝟙 ≫ j = j ≫ 𝟙`. -/
lemma sqIso_id_horiz_hom (j : X ⟶ Y) (w : 𝟙 X ≫ j = j ≫ 𝟙 Y) :
    (F.sqIso (𝟙 X) j j (𝟙 Y) w).hom =
      Functor.whiskerLeft (F.pb j) (F.pbId X).hom ≫ (Functor.rightUnitor _).hom ≫
        (Functor.leftUnitor _).inv ≫ Functor.whiskerRight (F.pbId Y).inv (F.pb j) := by
  rw [F.sqIso_eq _ _ _ _ w j (Category.id_comp j) (Category.comp_id j)]
  ext M
  simp [pbComp'_id_left_inv_app, pbComp'_id_right_hom_app]

/-- The square isomorphism of the square `g ≫ 𝟙 = 𝟙 ≫ g`. -/
lemma sqIso_id_vert_hom (g : X ⟶ Y) (w : g ≫ 𝟙 Y = 𝟙 X ≫ g) :
    (F.sqIso g (𝟙 X) (𝟙 Y) g w).hom =
      Functor.whiskerRight (F.pbId Y).hom (F.pb g) ≫ (Functor.leftUnitor _).hom ≫
        (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft (F.pb g) (F.pbId X).inv := by
  rw [F.sqIso_eq _ _ _ _ w g (Category.comp_id g) (Category.id_comp g)]
  ext M
  simp [pbComp'_id_left_hom_app, pbComp'_id_right_inv_app]

end Unit


section IdentitySquares

variable [𝒪.ContainsIdentities] {X Y : 𝒞}

omit [𝒪.ContainsIdentities] in
/-- The base change map of the square `𝟙 ≫ j = j ≫ 𝟙` is the identity, up to `(𝟙)^* ≅ 𝟭`. -/
lemma baseChange_id_horiz (j : X ⟶ Y) [Fact (𝒪 j)] (w : 𝟙 X ≫ j = j ≫ 𝟙 Y) :
    F.baseChange (𝟙 X) j j (𝟙 Y) w =
      ((TwoSquare.mk (𝟭 _) (F.sh j) (F.sh j) (𝟭 _)
        ((Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv)).whiskerTop
          (F.pbId X).hom).whiskerBottom (F.pbId Y).inv := by
  apply (mateEquiv (F.shAdj j) (F.shAdj j)).injective
  rw [mateEquiv_whiskerTop_whiskerBottom, mateEquiv_unitors]
  simp only [baseChange, Equiv.apply_symm_apply, F.sqIso_id_horiz_hom]
  ext M
  simp

/-- The base change map of the square `g ≫ 𝟙 = 𝟙 ≫ g` is the identity, up to `(𝟙)_! ≅ 𝟭`. -/
lemma baseChange_id_vert (g : X ⟶ Y) (w : g ≫ 𝟙 Y = 𝟙 X ≫ g) :
    F.baseChange g (𝟙 X) (𝟙 Y) g w =
      ((TwoSquare.mk (F.pb g) (𝟭 _) (𝟭 _) (F.pb g)
        ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)).whiskerLeft
          (F.shId Y).inv).whiskerRight (F.shId X).hom := by
  apply (mateEquiv (F.shAdj (𝟙 Y)) (F.shAdj (𝟙 X))).injective
  rw [mateEquiv_conjugateEquiv_vcomp _ Adjunction.id, conjugateEquiv_mateEquiv_vcomp _
    Adjunction.id, mateEquiv_id_id_unitors]
  have h₁ : conjugateEquiv (F.shAdj (𝟙 Y)) Adjunction.id (F.shId Y).inv = (F.pbId Y).hom := by
    simp [shId, conjugateIsoEquiv]
  have h₂ : conjugateEquiv Adjunction.id (F.shAdj (𝟙 X)) (F.shId X).hom = (F.pbId X).inv := by
    simp [shId, conjugateIsoEquiv]
  rw [h₁, h₂]
  simp only [baseChange, Equiv.apply_symm_apply, F.sqIso_id_vert_hom]
  ext M
  simp

omit [𝒪.ContainsIdentities] in
/-- The exchange map of the square `𝟙 ≫ j = j ≫ 𝟙` is the identity, up to `(𝟙)_* ≅ 𝟭`. -/
lemma exchange_id_horiz (j : X ⟶ Y) [Fact (𝒪 j)] (w : 𝟙 X ≫ j = j ≫ 𝟙 Y)
    [IsIso (F.baseChange (𝟙 X) j j (𝟙 Y) w)] :
    F.exchange (𝟙 X) j j (𝟙 Y) w =
      ((TwoSquare.mk (𝟭 _) (F.sh j) (F.sh j) (𝟭 _)
        ((Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv)).whiskerTop
          (F.pfId X).hom).whiskerBottom (F.pfId Y).inv := by
  have key : inv (F.baseChange (𝟙 X) j j (𝟙 Y) w) =
      ((TwoSquare.mk (F.sh j) (𝟭 _) (𝟭 _) (F.sh j)
        ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)).whiskerLeft
          (F.pbId X).inv).whiskerRight (F.pbId Y).hom := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [F.baseChange_id_horiz j w]
    ext M
    simp [← Functor.map_comp]
  rw [exchange, key, mateEquiv_conjugateEquiv_vcomp _ Adjunction.id,
    conjugateEquiv_mateEquiv_vcomp _ Adjunction.id, mateEquiv_id_id_unitors]
  rfl

/-- The exchange map of the square `g ≫ 𝟙 = 𝟙 ≫ g` is the identity, up to `(𝟙)_! ≅ 𝟭`. -/
lemma exchange_id_vert (g : X ⟶ Y) (w : g ≫ 𝟙 Y = 𝟙 X ≫ g)
    [IsIso (F.baseChange g (𝟙 X) (𝟙 Y) g w)] :
    F.exchange g (𝟙 X) (𝟙 Y) g w =
      ((TwoSquare.mk (F.pf g) (𝟭 _) (𝟭 _) (F.pf g)
        ((Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv)).whiskerRight
          (F.shId Y).hom).whiskerLeft (F.shId X).inv := by
  have key : inv (F.baseChange g (𝟙 X) (𝟙 Y) g w) =
      ((TwoSquare.mk (𝟭 _) (F.pb g) (F.pb g) (𝟭 _)
        ((Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv)).whiskerTop
          (F.shId Y).hom).whiskerBottom (F.shId X).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [F.baseChange_id_vert g w]
    ext M
    simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.whiskerTop,
      TwoSquare.whiskerBottom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Category.id_comp,
      Category.assoc, NatTrans.id_app, Functor.comp_obj, Functor.id_obj]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  rw [exchange, key, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_unitors]

end IdentitySquares


section PushforwardUnit

variable {X Y : 𝒞}

lemma pfId_hom : (F.pfId X).hom = conjugateEquiv (F.adj (𝟙 X)) Adjunction.id (F.pbId X).inv :=
  rfl

lemma pfId_inv : (F.pfId X).inv = conjugateEquiv Adjunction.id (F.adj (𝟙 X)) (F.pbId X).hom :=
  rfl

/-- The left unit law for the composition isomorphisms of the pushforwards. -/
lemma pfComp'_id_left (f : X ⟶ Y) :
    (F.pfComp' (𝟙 X) f f (Category.id_comp f)).hom ≫
        Functor.whiskerRight (F.pfId X).hom (F.pf f) ≫ (Functor.leftUnitor (F.pf f)).hom =
      𝟙 _ := by
  have hl : conjugateEquiv ((F.adj f).comp Adjunction.id) (F.adj f)
      (Functor.rightUnitor (F.pb f)).inv = (Functor.leftUnitor (F.pf f)).hom :=
    congrArg Iso.inv (conjugateIsoEquiv_rightUnitor (F.adj f))
  have hpb : (Functor.rightUnitor (F.pb f)).inv ≫
      Functor.whiskerLeft (F.pb f) (F.pbId X).inv ≫
        (F.pbComp' (𝟙 X) f f (Category.id_comp f)).inv = 𝟙 _ := by
    ext M
    simp [pbComp'_id_left_inv_app]
  rw [pfComp'_hom, pfId_hom, ← conjugateEquiv_whiskerLeft _ _ (F.adj f), ← hl,
    conjugateEquiv_comp, conjugateEquiv_comp, Category.assoc, hpb, conjugateEquiv_id]

/-- The right unit law for the composition isomorphisms of the pushforwards. -/
lemma pfComp'_id_right (f : X ⟶ Y) :
    (F.pfComp' f (𝟙 Y) f (Category.comp_id f)).hom ≫
        Functor.whiskerLeft (F.pf f) (F.pfId Y).hom ≫ (Functor.rightUnitor (F.pf f)).hom =
      𝟙 _ := by
  have hr : conjugateEquiv (Adjunction.id.comp (F.adj f)) (F.adj f)
      (Functor.leftUnitor (F.pb f)).inv = (Functor.rightUnitor (F.pf f)).hom :=
    congrArg Iso.inv (conjugateIsoEquiv_leftUnitor (F.adj f))
  have hpb : (Functor.leftUnitor (F.pb f)).inv ≫
      Functor.whiskerRight (F.pbId Y).inv (F.pb f) ≫
        (F.pbComp' f (𝟙 Y) f (Category.comp_id f)).inv = 𝟙 _ := by
    ext M
    simp [pbComp'_id_right_inv_app, ← Functor.map_comp]
  rw [pfComp'_hom, pfId_hom, ← conjugateEquiv_whiskerRight _ _ (F.adj f), ← hr,
    conjugateEquiv_comp, conjugateEquiv_comp, Category.assoc, hpb, conjugateEquiv_id]


lemma pfComp'_id_left_inv_app (f : X ⟶ Y) (M : F.obj X) :
    (F.pfComp' (𝟙 X) f f (Category.id_comp f)).inv.app M =
      (F.pf f).map ((F.pfId X).hom.app M) := by
  rw [← cancel_epi ((F.pfComp' (𝟙 X) f f (Category.id_comp f)).hom.app M), Iso.hom_inv_id_app]
  simpa using (congr_app (F.pfComp'_id_left f) M).symm

lemma pfComp'_id_right_inv_app (f : X ⟶ Y) (M : F.obj X) :
    (F.pfComp' f (𝟙 Y) f (Category.comp_id f)).inv.app M =
      (F.pfId Y).hom.app ((F.pf f).obj M) := by
  rw [← cancel_epi ((F.pfComp' f (𝟙 Y) f (Category.comp_id f)).hom.app M), Iso.hom_inv_id_app]
  simpa using (congr_app (F.pfComp'_id_right f) M).symm


lemma pfComp'_id_left_hom_app (f : X ⟶ Y) (M : F.obj X) :
    (F.pfComp' (𝟙 X) f f (Category.id_comp f)).hom.app M =
      (F.pf f).map ((F.pfId X).inv.app M) := by
  rw [← cancel_mono ((F.pfComp' (𝟙 X) f f (Category.id_comp f)).inv.app M), Iso.hom_inv_id_app,
    pfComp'_id_left_inv_app, ← Functor.map_comp, Iso.inv_hom_id_app]
  exact (CategoryTheory.Functor.map_id _ _).symm


lemma pfComp'_id_right_hom_app (f : X ⟶ Y) (M : F.obj X) :
    (F.pfComp' f (𝟙 Y) f (Category.comp_id f)).hom.app M =
      (F.pfId Y).inv.app ((F.pf f).obj M) := by
  rw [← cancel_mono ((F.pfComp' f (𝟙 Y) f (Category.comp_id f)).inv.app M), Iso.hom_inv_id_app,
    pfComp'_id_right_inv_app, Iso.inv_hom_id_app]
  rfl

end PushforwardUnit


section ExtensionByZeroUnit

variable [𝒪.ContainsIdentities] {X Y : 𝒞}

/-- The left unit law for the composition isomorphisms of the extensions by zero. -/
lemma shComp'_id_left (j : X ⟶ Y) [Fact (𝒪 j)] :
    (F.shComp' (𝟙 X) j j (Category.id_comp j)).hom ≫
        Functor.whiskerRight (F.shId X).hom (F.sh j) ≫ (Functor.leftUnitor (F.sh j)).hom =
      𝟙 _ := by
  apply (conjugateEquiv (F.shAdj j) (F.shAdj j)).injective
  have h₁ : conjugateEquiv ((F.shAdj (𝟙 X)).comp (F.shAdj j)) (F.shAdj j)
      (F.shComp' (𝟙 X) j j (Category.id_comp j)).hom =
        (F.pbComp' (𝟙 X) j j (Category.id_comp j)).inv := by
    simp [shComp', conjugateIsoEquiv]
  have h₂ : conjugateEquiv Adjunction.id (F.shAdj (𝟙 X)) (F.shId X).hom = (F.pbId X).inv := by
    simp [shId, conjugateIsoEquiv]
  rw [conjugateEquiv_id, ← conjugateEquiv_comp _ ((F.shAdj (𝟙 X)).comp (F.shAdj j)),
    ← conjugateEquiv_comp _ (Adjunction.id.comp (F.shAdj j)), conjugateEquiv_leftUnitor_hom,
    conjugateEquiv_whiskerRight, h₁, h₂]
  ext M
  simp [pbComp'_id_left_inv_app]

/-- The right unit law for the composition isomorphisms of the extensions by zero. -/
lemma shComp'_id_right (j : X ⟶ Y) [Fact (𝒪 j)] :
    (F.shComp' j (𝟙 Y) j (Category.comp_id j)).hom ≫
        Functor.whiskerLeft (F.sh j) (F.shId Y).hom ≫ (Functor.rightUnitor (F.sh j)).hom =
      𝟙 _ := by
  apply (conjugateEquiv (F.shAdj j) (F.shAdj j)).injective
  have h₁ : conjugateEquiv ((F.shAdj j).comp (F.shAdj (𝟙 Y))) (F.shAdj j)
      (F.shComp' j (𝟙 Y) j (Category.comp_id j)).hom =
        (F.pbComp' j (𝟙 Y) j (Category.comp_id j)).inv := by
    simp [shComp', conjugateIsoEquiv]
  have h₂ : conjugateEquiv Adjunction.id (F.shAdj (𝟙 Y)) (F.shId Y).hom = (F.pbId Y).inv := by
    simp [shId, conjugateIsoEquiv]
  rw [conjugateEquiv_id, ← conjugateEquiv_comp _ ((F.shAdj j).comp (F.shAdj (𝟙 Y))),
    ← conjugateEquiv_comp _ ((F.shAdj j).comp Adjunction.id), conjugateEquiv_rightUnitor_hom,
    conjugateEquiv_whiskerLeft, h₁, h₂]
  ext M
  simp [pbComp'_id_right_inv_app, ← Functor.map_comp]


/-- The identity isomorphism `(𝟙 X)_! ≅ 𝟭` is characterized by the counit of `(𝟙 X)_! ⊣ (𝟙 X)^*`:
`(𝟙 X)^* W ≅ (𝟙 X)_! (𝟙 X)^* W ⟶ W` is `(𝟙 X)^* ≅ 𝟭`. -/
@[reassoc]
lemma shId_inv_app_comp_counit (X : 𝒞) (W : F.obj X) :
    (F.shId X).inv.app ((F.pb (𝟙 X)).obj W) ≫ (F.shAdj (𝟙 X)).counit.app W =
      (F.pbId X).hom.app W := by
  have h₂ : conjugateEquiv Adjunction.id (F.shAdj (𝟙 X)) (F.shId X).hom = (F.pbId X).inv := by
    simp [shId, conjugateIsoEquiv]
  have hc := conjugateEquiv_counit Adjunction.id (F.shAdj (𝟙 X)) (F.shId X).hom W
  rw [h₂] at hc
  simp only [Functor.id_obj, Adjunction.id_counit, NatTrans.id_app] at hc
  have hc' : (F.shAdj (𝟙 X)).counit.app W =
      (F.sh (𝟙 X)).map ((F.pbId X).hom.app W) ≫ (F.shId X).hom.app W := by
    rw [← cancel_epi ((F.sh (𝟙 X)).map ((F.pbId X).inv.app W)), ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    erw [hc]
    simp
  have hn := (F.shId X).inv.naturality ((F.pbId X).hom.app W)
  simp only [Functor.id_map] at hn
  rw [hc', ← reassoc_of% hn, Iso.inv_hom_id_app]
  simp

end ExtensionByZeroUnit


section Restriction

variable {U' U Z' Z : 𝒞}

/-- The base change map of the extension by zero becomes an isomorphism after restriction to the
open `l : U' ⟶ Z'`, when the extensions by zero along `l` and `r` are fully faithful. -/
lemma isIso_map_baseChange_app (t : U' ⟶ U) (l : U' ⟶ Z') (r : U ⟶ Z) (b : Z' ⟶ Z)
    [Fact (𝒪 l)] [Fact (𝒪 r)] (w : t ≫ r = l ≫ b) [IsIso (F.shAdj r).unit]
    [IsIso (F.shAdj l).unit] (M : F.obj U) :
    IsIso ((F.pb l).map ((F.baseChange t l r b w).app M)) := by
  have h := unit_mateEquiv_symm (F.shAdj r) (F.shAdj l) (F.sqIso t l r b w).hom M
  have h' : (F.pb l).map ((F.baseChange t l r b w).app M) =
      inv ((F.shAdj l).unit.app _) ≫ (F.pb t).map ((F.shAdj r).unit.app M) ≫
        (F.sqIso t l r b w).hom.app _ := by
    rw [IsIso.eq_inv_comp]
    exact h.symm
  rw [h']
  infer_instance

end Restriction

end CategoryTheory.ExchangeFormalism
