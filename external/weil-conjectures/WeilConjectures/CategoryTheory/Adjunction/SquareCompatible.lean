/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate

/-!
# Natural transformations compatible with commutation squares

Consider two "levels" of categories and functors, related by functors `T` going from the first
level to the second (think: extension of scalars along a morphism of coefficient rings). A
functor `F : A ⥤ B` of the first level and a functor `F' : A' ⥤ B'` of the second level are
related by a *commutation square* `ιF : F ⋙ T_B ≅ T_A ⋙ F'`. Two natural transformations
`α : F ⟶ G` and `α' : F' ⟶ G'` are *compatible* with commutation squares `ιF` and `ιG`
(`CategoryTheory.NatTrans.SquareCompatible`) if
`T_B (α_K) ≫ ιG_K = ιF_K ≫ α'_{T_A K}` for all `K`.

This file shows that compatibility is stable under composition, inversion, whiskering (with the
pasted squares `CategoryTheory.Functor.pasteSquareIso`) and the associators and unitors, and that
the units and counits of adjunctions are compatible with commutation squares of the left adjoints
and the commutation squares of the right adjoints obtained as their mates. Consequently the
exchange morphisms `CategoryTheory.Adjunction.exchangeRight` and
`CategoryTheory.Adjunction.exchangeLeft` and the conjugates of compatible transformations are
compatible with the commutation squares.

This is the formal part of the compatibility of the six operations with the coefficient
comparisons (blueprint `sk-thm-sf-compatibility` (7)).
-/

@[expose] public section

namespace CategoryTheory

section Paste

variable {A₁ A₂ A₃ B₁ B₂ B₃ : Type*} [Category* A₁] [Category* A₂] [Category* A₃]
  [Category* B₁] [Category* B₂] [Category* B₃]
  {F₁ : A₁ ⥤ A₂} {F₂ : A₂ ⥤ A₃} {F₁' : B₁ ⥤ B₂} {F₂' : B₂ ⥤ B₃}
  {T₁ : A₁ ⥤ B₁} {T₂ : A₂ ⥤ B₂} {T₃ : A₃ ⥤ B₃}

/-- The pasting `(F₁ ⋙ F₂) ⋙ T₃ ≅ T₁ ⋙ (F₁' ⋙ F₂')` of two commutation squares
`ι₁ : F₁ ⋙ T₂ ≅ T₁ ⋙ F₁'` and `ι₂ : F₂ ⋙ T₃ ≅ T₂ ⋙ F₂'`. -/
def Functor.pasteSquareIso (ι₁ : F₁ ⋙ T₂ ≅ T₁ ⋙ F₁') (ι₂ : F₂ ⋙ T₃ ≅ T₂ ⋙ F₂') :
    (F₁ ⋙ F₂) ⋙ T₃ ≅ T₁ ⋙ (F₁' ⋙ F₂') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F₁ ι₂ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ι₁ F₂' ≪≫ Functor.associator _ _ _

@[simp]
lemma Functor.pasteSquareIso_hom_app (ι₁ : F₁ ⋙ T₂ ≅ T₁ ⋙ F₁') (ι₂ : F₂ ⋙ T₃ ≅ T₂ ⋙ F₂')
    (K : A₁) :
    (Functor.pasteSquareIso ι₁ ι₂).hom.app K = ι₂.hom.app (F₁.obj K) ≫ F₂'.map (ι₁.hom.app K) := by
  simp [Functor.pasteSquareIso]

@[simp]
lemma Functor.pasteSquareIso_inv_app (ι₁ : F₁ ⋙ T₂ ≅ T₁ ⋙ F₁') (ι₂ : F₂ ⋙ T₃ ≅ T₂ ⋙ F₂')
    (K : A₁) :
    (Functor.pasteSquareIso ι₁ ι₂).inv.app K = F₂'.map (ι₁.inv.app K) ≫ ι₂.inv.app (F₁.obj K) := by
  simp [Functor.pasteSquareIso]

end Paste

/-- The identity commutation square `𝟭 A ⋙ T ≅ T ⋙ 𝟭 B` of a functor `T`. -/
def Functor.idSquareIso {A B : Type*} [Category* A] [Category* B] (T : A ⥤ B) :
    𝟭 A ⋙ T ≅ T ⋙ 𝟭 B :=
  Functor.leftUnitor T ≪≫ (Functor.rightUnitor T).symm

@[simp]
lemma Functor.idSquareIso_hom_app {A B : Type*} [Category* A] [Category* B] (T : A ⥤ B) (K : A) :
    (Functor.idSquareIso T).hom.app K = 𝟙 _ := by
  simp [Functor.idSquareIso]

@[simp]
lemma Functor.idSquareIso_inv_app {A B : Type*} [Category* A] [Category* B] (T : A ⥤ B) (K : A) :
    (Functor.idSquareIso T).inv.app K = 𝟙 _ := by
  simp [Functor.idSquareIso]

section Compatible

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {T : A ⥤ A'} {T' : B ⥤ B'}

/-- The natural transformations `α : F ⟶ G` and `α' : F' ⟶ G'` are *compatible* with the
commutation squares `ιF : F ⋙ T' ≅ T ⋙ F'` and `ιG : G ⋙ T' ≅ T ⋙ G'`:
`T' (α_K) ≫ ιG_K = ιF_K ≫ α'_{T K}` for all `K`. -/
def NatTrans.SquareCompatible {F G : A ⥤ B} {F' G' : A' ⥤ B'} (ιF : F ⋙ T' ≅ T ⋙ F')
    (ιG : G ⋙ T' ≅ T ⋙ G') (α : F ⟶ G) (α' : F' ⟶ G') : Prop :=
  ∀ K, T'.map (α.app K) ≫ ιG.hom.app K = ιF.hom.app K ≫ α'.app (T.obj K)

namespace NatTrans.SquareCompatible

variable {F G H : A ⥤ B} {F' G' H' : A' ⥤ B'} {ιF : F ⋙ T' ≅ T ⋙ F'} {ιG : G ⋙ T' ≅ T ⋙ G'}
  {ιH : H ⋙ T' ≅ T ⋙ H'}

lemma app {α : F ⟶ G} {α' : F' ⟶ G'} (h : SquareCompatible ιF ιG α α') (K : A) :
    T'.map (α.app K) ≫ ιG.hom.app K = ιF.hom.app K ≫ α'.app (T.obj K) :=
  h K

lemma id (ι : F ⋙ T' ≅ T ⋙ F') : SquareCompatible ι ι (𝟙 F) (𝟙 F') := by
  intro K
  simp

lemma comp {α : F ⟶ G} {α' : F' ⟶ G'} {β : G ⟶ H} {β' : G' ⟶ H'}
    (h₁ : SquareCompatible ιF ιG α α') (h₂ : SquareCompatible ιG ιH β β') :
    SquareCompatible ιF ιH (α ≫ β) (α' ≫ β') := by
  intro K
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.map_comp, Category.assoc, h₂ K,
    reassoc_of% (h₁ K)]

lemma inv {e : F ≅ G} {e' : F' ≅ G'} (h : SquareCompatible ιF ιG e.hom e'.hom) :
    SquareCompatible ιG ιF e.inv e'.inv := by
  intro K
  rw [← cancel_epi (T'.map (e.hom.app K)), ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp, reassoc_of% (h K), Iso.hom_inv_id_app, Category.comp_id]

lemma isIso_inv {α : F ⟶ G} {α' : F' ⟶ G'} [IsIso α] [IsIso α']
    (h : SquareCompatible ιF ιG α α') :
    SquareCompatible ιG ιF (CategoryTheory.inv α) (CategoryTheory.inv α') :=
  inv (e := asIso α) (e' := asIso α') h

lemma of_eq {ιF₁ ιF₂ : F ⋙ T' ≅ T ⋙ F'} {ιG₁ ιG₂ : G ⋙ T' ≅ T ⋙ G'} {α : F ⟶ G}
    {α' : F' ⟶ G'} (h : SquareCompatible ιF₁ ιG₁ α α') (hF : ιF₁ = ιF₂) (hG : ιG₁ = ιG₂) :
    SquareCompatible ιF₂ ιG₂ α α' := by
  subst hF hG
  exact h

lemma of_eq_natTrans {α β : F ⟶ G} {α' β' : F' ⟶ G'} (h : SquareCompatible ιF ιG α α')
    (hα : α = β) (hα' : α' = β') : SquareCompatible ιF ιG β β' := by
  subst hα hα'
  exact h


section Whisker

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']

lemma whiskerLeft {S : C ⥤ C'} {E : C ⥤ A} {E' : C' ⥤ A'} (ιE : E ⋙ T ≅ S ⋙ E')
    {α : F ⟶ G} {α' : F' ⟶ G'} (h : SquareCompatible ιF ιG α α') :
    SquareCompatible (Functor.pasteSquareIso ιE ιF) (Functor.pasteSquareIso ιE ιG)
      (Functor.whiskerLeft E α) (Functor.whiskerLeft E' α') := by
  intro K
  simp only [Functor.comp_obj, Functor.whiskerLeft_app, Functor.pasteSquareIso_hom_app]
  rw [reassoc_of% (h (E.obj K)), Category.assoc]
  exact congrArg (ιF.hom.app (E.obj K) ≫ ·) (α'.naturality (ιE.hom.app K)).symm

lemma whiskerRight {U : D ⥤ D'} {E : B ⥤ D} {E' : B' ⥤ D'} (ιE : E ⋙ U ≅ T' ⋙ E')
    {α : F ⟶ G} {α' : F' ⟶ G'} (h : SquareCompatible ιF ιG α α') :
    SquareCompatible (Functor.pasteSquareIso ιF ιE) (Functor.pasteSquareIso ιG ιE)
      (Functor.whiskerRight α E) (Functor.whiskerRight α' E') := by
  intro K
  simp only [Functor.comp_obj, Functor.whiskerRight_app, Functor.pasteSquareIso_hom_app]
  have := ιE.hom.naturality (α.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at this
  rw [reassoc_of% this, ← Functor.map_comp, h K, Functor.map_comp, Category.assoc]

end Whisker

section Associator

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  {S : C ⥤ C'} {U : D ⥤ D'} {F₁ : C ⥤ A} {F₂ : A ⥤ B} {F₃ : B ⥤ D} {F₁' : C' ⥤ A'}
  {F₂' : A' ⥤ B'} {F₃' : B' ⥤ D'}

lemma associator_hom (ι₁ : F₁ ⋙ T ≅ S ⋙ F₁') (ι₂ : F₂ ⋙ T' ≅ T ⋙ F₂')
    (ι₃ : F₃ ⋙ U ≅ T' ⋙ F₃') :
    SquareCompatible (Functor.pasteSquareIso (Functor.pasteSquareIso ι₁ ι₂) ι₃)
      (Functor.pasteSquareIso ι₁ (Functor.pasteSquareIso ι₂ ι₃))
      (Functor.associator F₁ F₂ F₃).hom (Functor.associator F₁' F₂' F₃').hom := by
  intro K
  simp

lemma associator_inv (ι₁ : F₁ ⋙ T ≅ S ⋙ F₁') (ι₂ : F₂ ⋙ T' ≅ T ⋙ F₂')
    (ι₃ : F₃ ⋙ U ≅ T' ⋙ F₃') :
    SquareCompatible (Functor.pasteSquareIso ι₁ (Functor.pasteSquareIso ι₂ ι₃))
      (Functor.pasteSquareIso (Functor.pasteSquareIso ι₁ ι₂) ι₃)
      (Functor.associator F₁ F₂ F₃).inv (Functor.associator F₁' F₂' F₃').inv := by
  intro K
  simp

end Associator

section Unitor

lemma leftUnitor_hom (ι : F ⋙ T' ≅ T ⋙ F') :
    SquareCompatible (Functor.pasteSquareIso (Functor.idSquareIso T) ι) ι
      (Functor.leftUnitor F).hom (Functor.leftUnitor F').hom := by
  intro K
  simp

lemma leftUnitor_inv (ι : F ⋙ T' ≅ T ⋙ F') :
    SquareCompatible ι (Functor.pasteSquareIso (Functor.idSquareIso T) ι)
      (Functor.leftUnitor F).inv (Functor.leftUnitor F').inv := by
  intro K
  simp

lemma rightUnitor_hom (ι : F ⋙ T' ≅ T ⋙ F') :
    SquareCompatible (Functor.pasteSquareIso ι (Functor.idSquareIso T')) ι
      (Functor.rightUnitor F).hom (Functor.rightUnitor F').hom := by
  intro K
  simp

lemma rightUnitor_inv (ι : F ⋙ T' ≅ T ⋙ F') :
    SquareCompatible ι (Functor.pasteSquareIso ι (Functor.idSquareIso T'))
      (Functor.rightUnitor F).inv (Functor.rightUnitor F').inv := by
  intro K
  simp

end Unitor

/-- A transformation out of `𝟭 ⋙ F` compatible with the pasting of the identity square and a
commutation square of `F` is compatible with the commutation square of `F`. -/
lemma of_pasteSquareIso_idSquareIso {α : F ⟶ G} {α' : F' ⟶ G'}
    (h : SquareCompatible (Functor.pasteSquareIso (Functor.idSquareIso T) ιF) ιG α α') :
    SquareCompatible ιF ιG α α' := by
  intro K
  simpa using h K

end NatTrans.SquareCompatible

end Compatible

end CategoryTheory
