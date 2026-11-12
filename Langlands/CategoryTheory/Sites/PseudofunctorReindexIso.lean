import Langlands.CategoryTheory.Sites.StackPullback
import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
import Mathlib.CategoryTheory.Bicategory.Functor.Cat

/-! # Strong transformations of reindexed pseudofunctors from natural isomorphisms -/

universe v₁ v₂ v₃ v' u₁ u₂ u₃ u'

open CategoryTheory CategoryTheory.Bicategory Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CategoryTheory.PseudofunctorReindexIso

open Langlands.CategoryTheory.StackPullback

/-- A strong transformation between category-valued pseudofunctors on a locally
discrete bicategory, from component functors, naturality isomorphisms and the two
coherence identities checked on objects. -/
def catStrongTrans {B₀ : Type*} [Category* B₀]
    (F G : LocallyDiscrete B₀ ⥤ᵖ Cat.{v', u'})
    (A : ∀ a : B₀, F.obj (.mk a) ⥤ G.obj (.mk a))
    (n : ∀ {a b : B₀} (h : a ⟶ b),
      (F.map h.toLoc).toFunctor ⋙ A b ≅ A a ⋙ (G.map h.toLoc).toFunctor)
    (hi : ∀ (a : B₀) (L : F.obj (.mk a)),
      (n (𝟙 a)).hom.app L ≫ (G.mapId (.mk a)).hom.toNatTrans.app ((A a).obj L) =
        (A a).map ((F.mapId (.mk a)).hom.toNatTrans.app L))
    (hc : ∀ {a b c : B₀} (h : a ⟶ b) (k : b ⟶ c) (L : F.obj (.mk a)),
      (n (h ≫ k)).hom.app L ≫ (G.mapComp h.toLoc k.toLoc).hom.toNatTrans.app ((A a).obj L) =
        (A c).map ((F.mapComp h.toLoc k.toLoc).hom.toNatTrans.app L) ≫
          (n k).hom.app ((F.map h.toLoc).toFunctor.obj L) ≫
            (G.map k.toLoc).toFunctor.map ((n h).hom.app L)) :
    Pseudofunctor.StrongTrans F G where
  app a := (A a.as).toCatHom
  naturality h := Cat.Hom.isoMk (n h.as)
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    have hη : η = 𝟙 _ := Subsingleton.elim _ _
    subst hη
    simp only [PrelaxFunctor.map₂_id, id_whiskerRight,
      whiskerLeft_id, Category.id_comp, Category.comp_id]
  naturality_id a := by
    rcases a with ⟨a⟩
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext L
    change (n (𝟙 a)).hom.app L ≫
        (G.mapId (.mk a)).hom.toNatTrans.app ((A a).obj L) =
      (A a).map ((F.mapId (.mk a)).hom.toNatTrans.app L) ≫ 𝟙 _ ≫ 𝟙 _
    simpa only [Category.comp_id] using hi a L
  naturality_comp {a b c} h k := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    rcases c with ⟨c⟩
    rcases h with ⟨h⟩
    rcases k with ⟨k⟩
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext L
    change (n (h ≫ k)).hom.app L ≫
        (G.mapComp h.toLoc k.toLoc).hom.toNatTrans.app ((A a).obj L) =
      (A c).map ((F.mapComp h.toLoc k.toLoc).hom.toNatTrans.app L) ≫ 𝟙 _ ≫
        (n k).hom.app ((F.map h.toLoc).toFunctor.obj L) ≫ 𝟙 _ ≫
          (G.map k.toLoc).toFunctor.map ((n h).hom.app L) ≫ 𝟙 _
    simpa only [Category.comp_id, Category.id_comp, Category.assoc] using hc h k L

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] (P : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- The composition comparison of a reindexed pseudofunctor is the flexible
composition comparison of the original one on image arrows. -/
lemma mapComp_reindex (G : C ⥤ E) {X Y Z : C} (h₁ : Y ⟶ X) (h₂ : Z ⟶ Y) :
    (reindex G P).mapComp h₁.op.toLoc h₂.op.toLoc =
      P.mapComp' (G.map h₁).op.toLoc (G.map h₂).op.toLoc (G.map (h₂ ≫ h₁)).op.toLoc
        (by rw [G.map_comp]; rfl) := by
  rw [← Pseudofunctor.mapComp'_eq_mapComp]
  exact mapComp'_reindex G P h₂ h₁ (h₂ ≫ h₁) rfl

/-- The identity comparison of a reindexed pseudofunctor is the flexible identity
comparison of the original one on the image of the identity. -/
lemma mapId_reindex (G : C ⥤ E) (X : C) :
    (reindex G P).mapId (.mk (op X)) =
      P.mapId' (G.map (𝟙 X)).op.toLoc (by rw [G.map_id]; rfl) := by
  ext
  simp [Pseudofunctor.mapId', PrelaxFunctor.map₂Iso_eqToIso]

/-- Equalities of composites in `E` give equalities of the opposite composites. -/
lemma op_toLoc_comp_eq {A B B' : E} {u : A ⟶ B} {v : B ⟶ B'} {w : A ⟶ B'}
    (h : u ≫ v = w) : v.op.toLoc ≫ u.op.toLoc = w.op.toLoc := by
  subst h
  rfl

variable {G₁ : C ⥤ E} {Φ : C ⥤ D} {G₂ : D ⥤ E} (θ : G₁ ≅ Φ ⋙ G₂)

/-- Pullback along the inverse comparison of the two composite functors. -/
abbrev component (X : C) :
    P.obj (.mk (op (G₁.obj X))) ⥤ P.obj (.mk (op (G₂.obj (Φ.obj X)))) :=
  (P.map (θ.inv.app X).op.toLoc).toFunctor

/-- The naturality square of the inverse comparison, read in `Eᵒᵖ`. -/
lemma inv_comm {X Y : C} (h : Y ⟶ X) :
    (θ.inv.app X).op.toLoc ≫ (G₂.map (Φ.map h)).op.toLoc =
      (θ.inv.app Y ≫ G₁.map h).op.toLoc := by
  rw [← θ.inv.naturality h]
  rfl

/-- The naturality isomorphism: two composition comparisons through the common
composite `θ.inv.app Y ≫ G₁.map h`. -/
def naturalityIso {X Y : C} (h : Y ⟶ X) :
    (P.map (G₁.map h).op.toLoc).toFunctor ⋙ component P θ Y ≅
      component P θ X ⋙ (P.map (G₂.map (Φ.map h)).op.toLoc).toFunctor :=
  Cat.Hom.toNatIso ((P.mapComp' (G₁.map h).op.toLoc (θ.inv.app Y).op.toLoc
      (θ.inv.app Y ≫ G₁.map h).op.toLoc rfl).symm ≪≫
    P.mapComp' (θ.inv.app X).op.toLoc (G₂.map (Φ.map h)).op.toLoc
      (θ.inv.app Y ≫ G₁.map h).op.toLoc (inv_comm θ h))

lemma naturalityIso_hom_app {X Y : C} (h : Y ⟶ X) (L : P.obj (.mk (op (G₁.obj X)))) :
    (naturalityIso P θ h).hom.app L =
      (P.mapComp' (G₁.map h).op.toLoc (θ.inv.app Y).op.toLoc
        (θ.inv.app Y ≫ G₁.map h).op.toLoc rfl).inv.toNatTrans.app L ≫
      (P.mapComp' (θ.inv.app X).op.toLoc (G₂.map (Φ.map h)).op.toLoc
        (θ.inv.app Y ≫ G₁.map h).op.toLoc (inv_comm θ h)).hom.toNatTrans.app L :=
  rfl

/-- Oplax functoriality of the naturality isomorphisms, on objects. -/
lemma naturalityIso_comp {X Y Z : C} (h₁ : Y ⟶ X) (h₂ : Z ⟶ Y)
    (L : P.obj (.mk (op (G₁.obj X)))) :
    (naturalityIso P θ (h₂ ≫ h₁)).hom.app L ≫
        ((reindex Φ (reindex G₂ P)).mapComp h₁.op.toLoc h₂.op.toLoc).hom.toNatTrans.app
          ((component P θ X).obj L) =
      (component P θ Z).map
          (((reindex G₁ P).mapComp h₁.op.toLoc h₂.op.toLoc).hom.toNatTrans.app L) ≫
        (naturalityIso P θ h₂).hom.app ((P.map (G₁.map h₁).op.toLoc).toFunctor.obj L) ≫
          (P.map (G₂.map (Φ.map h₂)).op.toLoc).toFunctor.map
            ((naturalityIso P θ h₁).hom.app L) := by
  rw [mapComp_reindex, mapComp_reindex,
    mapComp'_reindex G₂ P _ _ _ (Φ.map_comp h₂ h₁).symm]
  simp only [naturalityIso_hom_app, Functor.map_comp, Category.assoc]
  have hθ : G₂.map (Φ.map h₂) ≫ θ.inv.app Y = θ.inv.app Z ≫ G₁.map h₂ :=
    θ.inv.naturality h₂
  rw [P.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app (θ.inv.app X).op.toLoc
    (G₂.map (Φ.map h₁)).op.toLoc (G₂.map (Φ.map h₂)).op.toLoc
    (θ.inv.app Y ≫ G₁.map h₁).op.toLoc (G₂.map (Φ.map (h₂ ≫ h₁))).op.toLoc
    (θ.inv.app Z ≫ G₁.map (h₂ ≫ h₁)).op.toLoc (inv_comm θ h₁)
    (op_toLoc_comp_eq (by rw [Φ.map_comp, G₂.map_comp])) (inv_comm θ (h₂ ≫ h₁))]
  rw [P.mapComp'₀₂₃_hom_app (G₁.map h₁).op.toLoc (θ.inv.app Y).op.toLoc
    (G₂.map (Φ.map h₂)).op.toLoc (θ.inv.app Y ≫ G₁.map h₁).op.toLoc
    (θ.inv.app Z ≫ G₁.map h₂).op.toLoc (θ.inv.app Z ≫ G₁.map (h₂ ≫ h₁)).op.toLoc rfl
    (inv_comm θ h₂)
    (op_toLoc_comp_eq (by rw [reassoc_of% hθ, G₁.map_comp]))]
  simp only [Category.assoc]
  rw [P.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app_assoc (G₁.map h₁).op.toLoc
    (G₁.map h₂).op.toLoc (θ.inv.app Z).op.toLoc (G₁.map (h₂ ≫ h₁)).op.toLoc
    (θ.inv.app Z ≫ G₁.map h₂).op.toLoc (θ.inv.app Z ≫ G₁.map (h₂ ≫ h₁)).op.toLoc
    (op_toLoc_comp_eq (G₁.map_comp h₂ h₁).symm) rfl
    (op_toLoc_comp_eq (by simp))]

/-- The identity comparison of a twice reindexed pseudofunctor. -/
lemma mapId_reindex_reindex (X : C) :
    (reindex Φ (reindex G₂ P)).mapId (.mk (op X)) =
      P.mapId' (G₂.map (Φ.map (𝟙 X))).op.toLoc (by rw [Φ.map_id, G₂.map_id]; rfl) := by
  ext
  simp [Pseudofunctor.mapId', PrelaxFunctor.map₂Iso_eqToIso]

omit [Category.{v₁} C] [Category.{v₂} D] in
/-- Unit coherence of the two composition comparisons through a common composite. -/
lemma mapComp'_mapId'_aux {A B : E} (t : B ⟶ A) (a : A ⟶ A) (b : B ⟶ B) (w : B ⟶ A)
    (ha : a = 𝟙 A) (hb : b = 𝟙 B) (h₁ : t ≫ a = w) (h₂ : b ≫ t = w)
    (L : P.obj (.mk (op A))) :
    (P.mapComp' a.op.toLoc t.op.toLoc w.op.toLoc (op_toLoc_comp_eq h₁)).inv.toNatTrans.app L ≫
        (P.mapComp' t.op.toLoc b.op.toLoc w.op.toLoc
          (op_toLoc_comp_eq h₂)).hom.toNatTrans.app L ≫
          (P.mapId' b.op.toLoc (by rw [hb]; rfl)).hom.toNatTrans.app
            ((P.map t.op.toLoc).toFunctor.obj L) =
      (P.map t.op.toLoc).toFunctor.map
        ((P.mapId' a.op.toLoc (by rw [ha]; rfl)).hom.toNatTrans.app L) := by
  subst ha hb
  have hw : w = t := h₁.symm.trans (Category.comp_id t)
  subst hw
  simp only [op_id, Quiver.Hom.id_toLoc, Pseudofunctor.mapId'_eq_mapId]
  rw [Pseudofunctor.mapComp'_id_comp_inv_app, Pseudofunctor.mapComp'_comp_id_hom_app]
  simp

/-- Oplax unity of the naturality isomorphisms, on objects. -/
lemma naturalityIso_id (X : C) (L : P.obj (.mk (op (G₁.obj X)))) :
    (naturalityIso P θ (𝟙 X)).hom.app L ≫
        ((reindex Φ (reindex G₂ P)).mapId (.mk (op X))).hom.toNatTrans.app
          ((component P θ X).obj L) =
      (component P θ X).map (((reindex G₁ P).mapId (.mk (op X))).hom.toNatTrans.app L) := by
  rw [mapId_reindex_reindex, mapId_reindex, naturalityIso_hom_app, Category.assoc]
  exact mapComp'_mapId'_aux P (θ.inv.app X) (G₁.map (𝟙 X)) (G₂.map (Φ.map (𝟙 X)))
    (θ.inv.app X ≫ G₁.map (𝟙 X)) (G₁.map_id X) (by rw [Φ.map_id, G₂.map_id]; rfl) rfl
    (θ.inv.naturality (𝟙 X)) L

/-- The strong transformation induced by `θ`: its component at `X` pulls back along
`θ.inv.app X`, and its naturality isomorphisms are `naturalityIso`. -/
def strongTrans :
    Pseudofunctor.StrongTrans (reindex G₁ P) (reindex Φ (reindex G₂ P)) :=
  catStrongTrans (reindex G₁ P) (reindex Φ (reindex G₂ P))
    (fun a ↦ component P θ a.unop)
    (fun h ↦ naturalityIso P θ h.unop)
    (fun a L ↦ naturalityIso_id P θ a.unop L)
    (fun h k L ↦ naturalityIso_comp P θ h.unop k.unop L)

@[simp]
lemma strongTrans_app (X : C) :
    ((strongTrans P θ).app (.mk (op X))).toFunctor = component P θ X := rfl

omit [Category.{v₁} C] [Category.{v₂} D] in
/-- Pullback along an isomorphism of `E` is an equivalence of fibres. -/
def mapIsoEquivalence {A B : E} (t : B ≅ A) :
    P.obj (.mk (op A)) ≌ P.obj (.mk (op B)) :=
  CategoryTheory.Equivalence.mk (P.map t.hom.op.toLoc).toFunctor (P.map t.inv.op.toLoc).toFunctor
    (Cat.Hom.toNatIso ((P.mapId (.mk (op A))).symm ≪≫
      P.mapComp' t.hom.op.toLoc t.inv.op.toLoc (𝟙 _)
        ((op_toLoc_comp_eq t.inv_hom_id).trans rfl)))
    (Cat.Hom.toNatIso ((P.mapComp' t.inv.op.toLoc t.hom.op.toLoc (𝟙 _)
        ((op_toLoc_comp_eq t.hom_inv_id).trans rfl)).symm ≪≫ P.mapId (.mk (op B))))

/-- Every component of the induced strong transformation is fully faithful. -/
def strongTransFullyFaithful (X : C) :
    ((strongTrans P θ).app (.mk (op X))).toFunctor.FullyFaithful :=
  (mapIsoEquivalence P (θ.app X).symm).fullyFaithfulFunctor

end Langlands.CategoryTheory.PseudofunctorReindexIso
