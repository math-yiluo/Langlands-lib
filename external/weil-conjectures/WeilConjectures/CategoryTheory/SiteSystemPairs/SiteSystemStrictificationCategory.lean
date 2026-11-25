/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Equivalence

/-! # The pair-category construction for coherent systems

Source: Stacks Project, Categories, Tag 004A, applied fibrewise.
(blueprint: lem-weil-pbc-site-system-strictification-category)
-/

@[expose] public section

universe u v w u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory

namespace CategoryTheory.SiteSystemPairs

variable {I : Type u} [Preorder I] (C : I → Cat.{v₁, u₁})

/-- The stage-labelled objects used in the splitting construction of Stacks 004A. -/
structure Obj (i : I) where
  stage : I
  le : stage ≤ i
  obj : C stage

variable (U : ∀ (i j : I), i ≤ j → C i ⥤ C j)

/-- Evaluation of a labelled object at the current stage. -/
abbrev evalObj (i : I) (X : Obj C i) : C i := (U X.stage i X.le).obj X.obj

/-- The category of labelled objects, with arrows evaluated at the current stage. -/
abbrev Fiber (i : I) := InducedCategory (C i) (evalObj C U i)

/-- Evaluation is the fully faithful induced functor. -/
abbrev eval (i : I) : Fiber C U i ⥤ C i := inducedFunctor (evalObj C U i)

/-- The inclusion of the current stage. -/
def inclusion (i : I) : C i ⥤ Fiber C U i where
  obj X := ⟨i, le_rfl, X⟩
  map f := InducedCategory.homMk ((U i i le_rfl).map f)
  map_id X := by apply InducedCategory.hom_ext; exact (U i i le_rfl).map_id X
  map_comp f g := by apply InducedCategory.hom_ext; exact (U i i le_rfl).map_comp f g

variable (gamma : ∀ (i j k : I) (h : i ≤ j) (h' : j ≤ k),
  U i j h ⋙ U j k h' ≅ U i k (h.trans h'))

/-- Transition fixes labels and conjugates the evaluated arrow by the comparison. -/
def transition (i j : I) (h : i ≤ j) : Fiber C U i ⥤ Fiber C U j where
  obj X := ⟨X.stage, X.le.trans h, X.obj⟩
  map {X Y} f := InducedCategory.homMk
    ((gamma X.stage i j X.le h).inv.app X.obj ≫ (U i j h).map f.hom ≫
      (gamma Y.stage i j Y.le h).hom.app Y.obj)
  map_id X := by
    apply InducedCategory.hom_ext
    change (gamma X.stage i j X.le h).inv.app X.obj ≫
      (U i j h).map (𝟙 _) ≫ (gamma X.stage i j X.le h).hom.app X.obj = 𝟙 _
    rw [Functor.map_id]
    exact (congrArg (fun f ↦ (gamma X.stage i j X.le h).inv.app X.obj ≫ f)
      (Category.id_comp ((gamma X.stage i j X.le h).hom.app X.obj))).trans
      ((gamma X.stage i j X.le h).inv_hom_id_app X.obj)
  map_comp {X Y Z} f g := by
    apply InducedCategory.hom_ext
    change (gamma X.stage i j X.le h).inv.app X.obj ≫
      (U i j h).map (f.hom ≫ g.hom) ≫ (gamma Z.stage i j Z.le h).hom.app Z.obj =
      ((gamma X.stage i j X.le h).inv.app X.obj ≫ (U i j h).map f.hom ≫
        (gamma Y.stage i j Y.le h).hom.app Y.obj) ≫
      ((gamma Y.stage i j Y.le h).inv.app Y.obj ≫ (U i j h).map g.hom ≫
        (gamma Z.stage i j Z.le h).hom.app Z.obj)
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

/-- Evaluation intertwines transition with the original transition up to gamma. -/
def comparison (i j : I) (h : i ≤ j) :
    transition C U gamma i j h ⋙ eval C U j ≅ eval C U i ⋙ U i j h :=
  NatIso.ofComponents (fun X ↦ ((gamma X.stage i j X.le h).app X.obj).symm)
    (by
      intro X Y f
      change ((gamma X.stage i j X.le h).inv.app X.obj ≫ (U i j h).map f.hom ≫
        (gamma Y.stage i j Y.le h).hom.app Y.obj) ≫
          (gamma Y.stage i j Y.le h).inv.app Y.obj =
        (gamma X.stage i j X.le h).inv.app X.obj ≫ (U i j h).map f.hom
      simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj]
      exact congrArg (fun f ↦ (gamma X.stage i j X.le h).inv.app X.obj ≫ f)
        (Category.comp_id ((U i j h).map f.hom)))

variable (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))

private theorem normalized_map
    {A : Type u₁} {B : Type u₂} {E : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} E]
    (G : E ⥤ E) (hG : G = 𝟭 E) (K : A ⥤ E) (L : B ⥤ E)
    (a : K ⋙ G ≅ K) (b : L ⋙ G ≅ L)
    (ha : HEq a (Iso.refl K)) (hb : HEq b (Iso.refl L))
    (X : A) (Y : B) (f : K.obj X ⟶ L.obj Y) :
    a.inv.app X ≫ G.map f ≫ b.hom.app Y = f := by
  subst hG
  have ha' : a = Iso.refl K := eq_of_heq ha
  have hb' : b = Iso.refl L := eq_of_heq hb
  rw [ha', hb']
  simp

/-- Right normalization makes a self-transition strictly the identity. -/
theorem transition_id (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hgammaRight : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i k k h le_rfl) (Iso.refl (U i k h))) (i : I) :
    transition C U gamma i i le_rfl = 𝟭 (Fiber C U i) := by
  apply Functor.hext (fun X ↦ by cases X; rfl)
  intro X Y f
  apply heq_of_eq
  apply InducedCategory.hom_ext
  exact normalized_map (U i i le_rfl) (hUid i) (U X.stage i X.le) (U Y.stage i Y.le)
    (gamma X.stage i i X.le le_rfl) (gamma Y.stage i i Y.le le_rfl)
    (hgammaRight _ _ _) (hgammaRight _ _ _) X.obj Y.obj f.hom

/-- The cocycle makes consecutive transitions compose strictly. -/
theorem transition_comp
    (hgamma : ∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
      (gamma j k l h' h'').hom.app ((U i j h).obj X) ≫
          (gamma i j l h (h'.trans h'')).hom.app X =
        (U k l h'').map ((gamma i j k h h').hom.app X) ≫
          (gamma i k l (h.trans h') h'').hom.app X)
    (i j k : I) (h : i ≤ j) (h' : j ≤ k) :
    transition C U gamma i j h ⋙ transition C U gamma j k h' =
      transition C U gamma i k (h.trans h') := by
  refine Functor.hext (F := transition C U gamma i j h ⋙ transition C U gamma j k h')
    (G := transition C U gamma i k (h.trans h')) (fun X ↦ rfl) ?_
  intro X Y f
  apply heq_of_eq
  apply InducedCategory.hom_ext
  change (gamma X.stage j k (X.le.trans h) h').inv.app X.obj ≫
      (U j k h').map ((gamma X.stage i j X.le h).inv.app X.obj ≫
        (U i j h).map f.hom ≫ (gamma Y.stage i j Y.le h).hom.app Y.obj) ≫
      (gamma Y.stage j k (Y.le.trans h) h').hom.app Y.obj =
    (gamma X.stage i k X.le (h.trans h')).inv.app X.obj ≫
      (U i k (h.trans h')).map f.hom ≫
      (gamma Y.stage i k Y.le (h.trans h')).hom.app Y.obj
  apply (cancel_epi ((U j k h').map ((gamma X.stage i j X.le h).hom.app X.obj) ≫
    (gamma X.stage j k (X.le.trans h) h').hom.app X.obj)).mp
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [← Functor.map_comp_assoc]
  rw [← Category.assoc ((U j k h').map ((gamma X.stage i j X.le h).hom.app X.obj))]
  rw [← hgamma X.stage i j k X.le h h' X.obj]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hgamma Y.stage i j k Y.le h h' Y.obj]
  exact (gamma i j k h h').hom.naturality_assoc f.hom
    ((gamma Y.stage i k Y.le (h.trans h')).hom.app Y.obj)

/-- The strict diagram defined by the pair-category transitions. -/
def diagram
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hgammaRight : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i k k h le_rfl) (Iso.refl (U i k h)))
    (hgamma : ∀ (i j k l : I) (h : i ≤ j) (h' : j ≤ k) (h'' : k ≤ l) (X : C i),
      (gamma j k l h' h'').hom.app ((U i j h).obj X) ≫
          (gamma i j l h (h'.trans h'')).hom.app X =
        (U k l h'').map ((gamma i j k h h').hom.app X) ≫
          (gamma i k l (h.trans h') h'').hom.app X) : I ⥤ Cat.{v₁, max u u₁} where
  obj i := Cat.of (Fiber C U i)
  map f := (transition C U gamma _ _ (leOfHom f)).toCatHom
  map_id i := Cat.ext (transition_id C U gamma hUid hgammaRight i)
  map_comp f g := Cat.ext (transition_comp C U gamma hgamma _ _ _
    (leOfHom f) (leOfHom g)).symm

variable (D : Type v) [Category.{w} D] (v : ∀ i : I, C i ⥤ D)
  (delta : ∀ (i j : I) (h : i ≤ j), U i j h ⋙ v j ≅ v i)

/-- A coefficient functor retains the label, conjugating arrows by delta. -/
def coefficients (i : I) : Fiber C U i ⥤ D where
  obj X := (v X.stage).obj X.obj
  map {X Y} f := (delta X.stage i X.le).inv.app X.obj ≫ (v i).map f.hom ≫
    (delta Y.stage i Y.le).hom.app Y.obj
  map_id X := by
    change (delta X.stage i X.le).inv.app X.obj ≫
      (v i).map (𝟙 _) ≫ (delta X.stage i X.le).hom.app X.obj = 𝟙 _
    rw [Functor.map_id]
    exact (congrArg (fun f ↦ (delta X.stage i X.le).inv.app X.obj ≫ f)
      (Category.id_comp ((delta X.stage i X.le).hom.app X.obj))).trans
      ((delta X.stage i X.le).inv_hom_id_app X.obj)
  map_comp {X Y Z} f g := by
    change (delta X.stage i X.le).inv.app X.obj ≫
      (v i).map (f.hom ≫ g.hom) ≫ (delta Z.stage i Z.le).hom.app Z.obj =
      ((delta X.stage i X.le).inv.app X.obj ≫ (v i).map f.hom ≫
        (delta Y.stage i Y.le).hom.app Y.obj) ≫
      ((delta Y.stage i Y.le).inv.app Y.obj ≫ (v i).map g.hom ≫
        (delta Z.stage i Z.le).hom.app Z.obj)
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem normalized_natiso_map
    {A : Type u₁} [Category.{v₁} A] {E : Type v} [Category.{w} E]
    (G H : A ⥤ E) (hG : G = H) (a : G ≅ H) (ha : HEq a (Iso.refl H))
    {X Y : A} (f : X ⟶ Y) : a.inv.app X ≫ G.map f ≫ a.hom.app Y = H.map f := by
  subst hG
  rw [eq_of_heq ha]
  simp

/-- The identity comparison between the two representations at the later stage. -/
def theta
    (hUid : ∀ i : I, U i i le_rfl = 𝟭 (C i))
    (hgammaLeft : ∀ (i k : I) (h : i ≤ k),
      HEq (gamma i i k le_rfl h) (Iso.refl (U i k h)))
    (i j : I) (h : i ≤ j) :
    inclusion C U i ⋙ transition C U gamma i j h ≅ U i j h ⋙ inclusion C U j :=
  NatIso.ofComponents (fun X ↦ InducedCategory.isoMk
    (((eqToIso (hUid j)).app ((U i j h).obj X)).symm)) (by
      intro X Y f
      apply InducedCategory.hom_ext
      change ((gamma i i j le_rfl h).inv.app X ≫
          (U i j h).map ((U i i le_rfl).map f) ≫
          (gamma i i j le_rfl h).hom.app Y) ≫
            (eqToIso (hUid j)).inv.app ((U i j h).obj Y) =
        (eqToIso (hUid j)).inv.app ((U i j h).obj X) ≫
          (U j j le_rfl).map ((U i j h).map f)
      have hn := normalized_natiso_map (U i i le_rfl ⋙ U i j h) (U i j h)
        (by rw [hUid i]; rfl) (gamma i i j le_rfl h) (hgammaLeft i j h) f
      change (gamma i i j le_rfl h).inv.app X ≫
        (U i j h).map ((U i i le_rfl).map f) ≫ (gamma i i j le_rfl h).hom.app Y =
        (U i j h).map f at hn
      rw [hn]
      exact (eqToIso (hUid j)).inv.naturality ((U i j h).map f))

end CategoryTheory.SiteSystemPairs
