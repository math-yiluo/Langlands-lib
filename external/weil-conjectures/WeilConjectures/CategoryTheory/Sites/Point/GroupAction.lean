/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Sites.Point.Category
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# Points of a site with a group action

Let `Φ` be a point of a site `(C, J)` and let a group `G` act on its fibre functor
`Φ.fiber`, i.e. we are given a monoid map `act : G →* End Φ.fiber`. Then `G` acts on the fibre
`Φ.sheafFiber.obj F` of every abelian sheaf `F`, by `[X, x, t] ↦ [X, σ • x, t]`; this defines a
functor `Φ.sheafFiberAction act : Sheaf J Ab ⥤ Action Ab G`.

This functor has a right adjoint `Φ.equivariantSheafFunctor act`, sending `M` to the sheaf of
`G`-equivariant maps `X ↦ {f : Φ.fiber.obj X → M | f (σ • x) = σ • f x}`: a subsheaf of the
skyscraper sheaf at `Φ` with value `M`.

## Main definitions

- `CategoryTheory.GrothendieckTopology.Point.sheafFiberAction`: the fibre functor with its
  `G`-action.
- `CategoryTheory.GrothendieckTopology.Point.equivariantSheafFunctor`: the sheaves of
  equivariant maps.
- `CategoryTheory.GrothendieckTopology.Point.sheafFiberActionAdjunction`: the adjunction.
-/

@[expose] public section

universe w v u u'

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {G : Type u'} [Group G] (act : G →* End Φ.fiber)

/-- The endomorphism of the point `Φ` given by the action of `σ` on its fibre functor. -/
def actHom (σ : G) : Φ ⟶ Φ :=
  ⟨(act σ).asHom⟩

/-- The action of `σ` on the fibre of a presheaf: `[X, x, t] ↦ [X, σ • x, t]`. -/
noncomputable def presheafFiberAct (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (σ : G) :
    Φ.presheafFiber.obj P ⟶ Φ.presheafFiber.obj P :=
  (Hom.presheafFiber (Φ.actHom act σ)).app P

@[reassoc (attr := simp)]
lemma toPresheafFiber_presheafFiberAct (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (σ : G) (X : C)
    (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.presheafFiberAct act P σ =
      Φ.toPresheafFiber X ((act σ).asHom.app X x) P := by
  simp [presheafFiberAct, actHom]

lemma toPresheafFiber_presheafFiberAct_apply (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (σ : G) (X : C)
    (x : Φ.fiber.obj X) (t : P.obj (op X)) :
    (Φ.presheafFiberAct act P σ).hom (Φ.toPresheafFiber X x P t) =
      Φ.toPresheafFiber X ((act σ).asHom.app X x) P t :=
  congr($(Φ.toPresheafFiber_presheafFiberAct act P σ X x).hom t)

lemma act_mul_app (σ τ : G) (X : C) (x : Φ.fiber.obj X) :
    (act (σ * τ)).asHom.app X x = (act σ).asHom.app X ((act τ).asHom.app X x) := by
  rw [map_mul, End.mul_asHom]
  rfl

@[simp]
lemma act_one_app (X : C) (x : Φ.fiber.obj X) : (act 1).asHom.app X x = x := by
  rw [map_one, End.one_asHom]
  rfl

/-- The fibre of a presheaf, with its action of `G`. -/
noncomputable abbrev presheafFiberAction (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    Action AddCommGrpCat.{w} G where
  V := Φ.presheafFiber.obj P
  ρ :=
    { toFun σ := .of <| Φ.presheafFiberAct act P σ
      map_one' := by
        apply End.ext
        refine Φ.presheafFiber_hom_ext fun X x ↦ ?_
        rw [toPresheafFiber_presheafFiberAct, act_one_app, End.one_asHom, Category.comp_id]
      map_mul' σ τ := by
        apply End.ext
        refine Φ.presheafFiber_hom_ext fun X x ↦ ?_
        rw [toPresheafFiber_presheafFiberAct, End.mul_asHom, toPresheafFiber_presheafFiberAct_assoc,
          toPresheafFiber_presheafFiberAct, act_mul_app] }

@[simp]
lemma presheafFiberAction_V (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (Φ.presheafFiberAction act P).V = Φ.presheafFiber.obj P :=
  rfl

@[simp]
lemma presheafFiberAction_ρ (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (σ : G) :
    (Φ.presheafFiberAction act P).ρ σ = .of (Φ.presheafFiberAct act P σ) :=
  rfl

/-- The fibre functor on abelian sheaves, with the action of `G` on the fibres. -/
@[simps]
noncomputable def sheafFiberAction : Sheaf J AddCommGrpCat.{w} ⥤ Action AddCommGrpCat.{w} G where
  obj F := Φ.presheafFiberAction act F.obj
  map {F F'} f :=
    { hom := Φ.presheafFiber.map f.hom
      comm σ := by
        refine Φ.presheafFiber_hom_ext fun X x ↦ ?_
        rw [presheafFiberAction_ρ, presheafFiberAction_ρ, toPresheafFiber_presheafFiberAct_assoc]
        rw [toPresheafFiber_naturality]
        rw [toPresheafFiber_naturality_assoc, toPresheafFiber_presheafFiberAct] }

section equivariant

variable (M : Action AddCommGrpCat.{w} G)

/-- The `G`-equivariant maps `Φ.fiber.obj X → M`. -/
def equivariantMaps (X : C) : AddSubgroup (Φ.fiber.obj X → M.V) where
  carrier := {f | ∀ (σ : G) (x : Φ.fiber.obj X),
    f ((act σ).asHom.app X x) = (M.ρ σ).asHom.hom (f x)}
  zero_mem' σ x := by simp
  add_mem' {f g} hf hg σ x := by simp [hf σ x, hg σ x]
  neg_mem' {f} hf σ x := by simp [hf σ x]

lemma mem_equivariantMaps {X : C} (f : Φ.fiber.obj X → M.V) :
    f ∈ Φ.equivariantMaps act M X ↔
      ∀ (σ : G) (x : Φ.fiber.obj X), f ((act σ).asHom.app X x) = (M.ρ σ).asHom.hom (f x) :=
  Iff.rfl


/-- Precomposition with `Φ.fiber.map g` on equivariant maps. -/
def equivariantMapsComap {X Y : C} (g : Y ⟶ X) :
    Φ.equivariantMaps act M X →+ Φ.equivariantMaps act M Y where
  toFun f := ⟨fun y ↦ f.1 (Φ.fiber.map g y), fun σ y ↦ by
    dsimp only
    rw [← f.2 σ, ← NatTrans.naturality_apply]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma equivariantMapsComap_apply_coe {X Y : C} (g : Y ⟶ X) (f : Φ.equivariantMaps act M X)
    (y : Φ.fiber.obj Y) :
    (Φ.equivariantMapsComap act M g f).1 y = f.1 (Φ.fiber.map g y) :=
  rfl

/-- The presheaf of `G`-equivariant maps from the fibres of `Φ` to `M`. -/
@[simps]
def equivariantPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj X := AddCommGrpCat.of (Φ.equivariantMaps act M X.unop)
  map g := AddCommGrpCat.ofHom (Φ.equivariantMapsComap act M g.unop)
  map_id X := by
    ext f x
    simp [equivariantMapsComap]
  map_comp f g := by
    ext h x
    simp [equivariantMapsComap]

lemma equivariantPresheaf_map_apply_coe {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (f : (Φ.equivariantPresheaf act M).obj X) (y : Φ.fiber.obj Y.unop) :
    ((Φ.equivariantPresheaf act M).map g f).1 y = f.1 (Φ.fiber.map g.unop y) :=
  rfl


/-- Two elements of the fibre over `X` coming from the fibres over two objects of a covering
sieve also come from a common object of that sieve. -/
lemma exists_of_fiber_map_eq {X Y₁ Y₂ : C} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X) (y₁ : Φ.fiber.obj Y₁)
    (y₂ : Φ.fiber.obj Y₂) (h : Φ.fiber.map f₁ y₁ = Φ.fiber.map f₂ y₂) :
    ∃ (Z : C) (p₁ : Z ⟶ Y₁) (p₂ : Z ⟶ Y₂) (z : Φ.fiber.obj Z), p₁ ≫ f₁ = p₂ ≫ f₂ ∧
      Φ.fiber.map p₁ z = y₁ ∧ Φ.fiber.map p₂ z = y₂ := by
  let α₁ : Φ.fiber.elementsMk _ y₁ ⟶ Φ.fiber.elementsMk _ (Φ.fiber.map f₁ y₁) := ⟨f₁, rfl⟩
  let α₂ : Φ.fiber.elementsMk _ y₂ ⟶ Φ.fiber.elementsMk _ (Φ.fiber.map f₁ y₁) := ⟨f₂, h.symm⟩
  obtain ⟨z, q₁, q₂, fac⟩ := IsCofiltered.cospan α₁ α₂
  exact ⟨z.obj, q₁.hom, q₂.hom, z.val, congrArg (fun f ↦ f.hom) fac, q₁.map_val,
    q₂.map_val⟩

lemma isSheaf_equivariantPresheaf : Presheaf.IsSheaf J (Φ.equivariantPresheaf act M) := by
  refine Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat.{w}) ?_
  rw [isSheaf_iff_isSheaf_of_type]
  intro X R hR s hs
  -- the value at `x` of the amalgamation, computed from any lift of `x` to the sieve
  have key {Y₁ Y₂ : C} {f₁ : Y₁ ⟶ X} {f₂ : Y₂ ⟶ X} (h₁ : R f₁) (h₂ : R f₂)
      (y₁ : Φ.fiber.obj Y₁) (y₂ : Φ.fiber.obj Y₂)
      (h : Φ.fiber.map f₁ y₁ = Φ.fiber.map f₂ y₂) :
      (s f₁ h₁).1 y₁ = (s f₂ h₂).1 y₂ := by
    obtain ⟨Z, p₁, p₂, z, fac, rfl, rfl⟩ := Φ.exists_of_fiber_map_eq f₁ f₂ y₁ y₂ h
    exact congr_arg (fun g ↦ (Subtype.val g) z) (hs p₁ p₂ h₁ h₂ fac)
  choose Y f hf y hy using fun x ↦ Φ.jointly_surjective R hR x
  have hval {Y' : C} {f' : Y' ⟶ X} (h' : R f') (y' : Φ.fiber.obj Y') :
      (s (f (Φ.fiber.map f' y')) (hf _)).1 (y _) = (s f' h').1 y' :=
    key _ _ _ _ (hy _)
  let t : (Φ.equivariantPresheaf act M ⋙ forget AddCommGrpCat.{w}).obj (op X) :=
    ⟨fun x ↦ (s (f x) (hf x)).1 (y x), fun σ x ↦ by
      have := hval (hf x) ((act σ).asHom.app _ (y x))
      rw [← NatTrans.naturality_apply, hy] at this
      dsimp only
      rw [this, (s (f x) (hf x)).2 σ (y x)]⟩
  refine ⟨t, fun Y' f' h' ↦ Subtype.ext (funext fun y' ↦ hval h' y'), fun t' ht' ↦ ?_⟩
  refine Subtype.ext (funext fun x ↦ ?_)
  have := congr_arg (fun g ↦ (Subtype.val g) (y x)) (ht' (f x) (hf x))
  simp only at this
  rw [← this]
  change t'.1 x = t'.1 (Φ.fiber.map (f x) (y x))
  rw [hy]

/-- The sheaf of `G`-equivariant maps from the fibres of `Φ` to `M`. -/
@[simps]
def equivariantSheaf : Sheaf J AddCommGrpCat.{w} :=
  ⟨Φ.equivariantPresheaf act M, Φ.isSheaf_equivariantPresheaf act M⟩

end equivariant

/-- Postcomposition with a morphism `φ : M ⟶ N` of `G`-modules on equivariant maps. -/
def equivariantMapsMap {M N : Action AddCommGrpCat.{w} G} (φ : M ⟶ N) (X : C) :
    Φ.equivariantMaps act M X →+ Φ.equivariantMaps act N X where
  toFun f := ⟨fun x ↦ φ.hom.hom (f.1 x), fun σ x ↦ by
    dsimp only
    rw [f.2 σ x]
    exact congr($(φ.comm σ).hom (f.1 x))⟩
  map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _)

@[simp]
lemma equivariantMapsMap_apply_coe {M N : Action AddCommGrpCat.{w} G} (φ : M ⟶ N) {X : C}
    (f : Φ.equivariantMaps act M X) (x : Φ.fiber.obj X) :
    (Φ.equivariantMapsMap act φ X f).1 x = φ.hom.hom (f.1 x) :=
  rfl

/-- The functor sending `M` to the sheaf of `G`-equivariant maps from the fibres of `Φ`
to `M`. -/
@[simps]
def equivariantSheafFunctor : Action AddCommGrpCat.{w} G ⥤ Sheaf J AddCommGrpCat.{w} where
  obj M := Φ.equivariantSheaf act M
  map {M N} φ := ⟨{
    app X := AddCommGrpCat.ofHom (Φ.equivariantMapsMap act φ X.unop)
    naturality _ _ _ := rfl }⟩

/-- A section `t` over `X` gives the equivariant map `x ↦ [X, x, t]`. -/
noncomputable def toEquivariantMaps (F : Sheaf J AddCommGrpCat.{w}) (X : C) :
    F.obj.obj (op X) →+ Φ.equivariantMaps act ((Φ.sheafFiberAction act).obj F) X where
  toFun t := ⟨fun x ↦ Φ.toPresheafFiber X x F.obj t, fun σ x ↦
    (Φ.toPresheafFiber_presheafFiberAct_apply act F.obj σ _ x t).symm⟩
  map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _)

@[simp]
lemma toEquivariantMaps_apply_coe (F : Sheaf J AddCommGrpCat.{w}) {X : C}
    (t : F.obj.obj (op X)) (x : Φ.fiber.obj X) :
    (Φ.toEquivariantMaps act F X t).1 x = Φ.toPresheafFiber X x F.obj t :=
  rfl

/-- The unit of the adjunction: a section `t` over `X` gives the equivariant map
`x ↦ [X, x, t]`. -/
noncomputable def toEquivariantSheaf (F : Sheaf J AddCommGrpCat.{w}) :
    F ⟶ Φ.equivariantSheaf act ((Φ.sheafFiberAction act).obj F) :=
  ⟨{app X := AddCommGrpCat.ofHom (Φ.toEquivariantMaps act F X.unop)
    naturality X Y g := AddCommGrpCat.ext fun t ↦ by
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
      exact Subtype.ext (funext fun y ↦ Φ.toPresheafFiber_w_apply g.unop y F.obj t) }⟩

@[simp]
lemma toEquivariantSheaf_hom_app_apply_coe (F : Sheaf J AddCommGrpCat.{w}) (X : Cᵒᵖ)
    (t : F.obj.obj X) (x : Φ.fiber.obj X.unop) :
    ((Φ.toEquivariantSheaf act F).hom.app X t).1 x = Φ.toPresheafFiber X.unop x F.obj t :=
  rfl

/-- Evaluation at `x` of equivariant maps. -/
def evalEquivariantMaps (M : Action AddCommGrpCat.{w} G) (X : C) (x : Φ.fiber.obj X) :
    (Φ.equivariantPresheaf act M).obj (op X) ⟶ M.V :=
  AddCommGrpCat.ofHom
    { toFun f := f.1 x
      map_zero' := rfl
      map_add' _ _ := rfl }

@[simp]
lemma evalEquivariantMaps_apply (M : Action AddCommGrpCat.{w} G) (X : C) (x : Φ.fiber.obj X)
    (f : (Φ.equivariantPresheaf act M).obj (op X)) :
    Φ.evalEquivariantMaps act M X x f = f.1 x :=
  rfl

lemma evalEquivariantMaps_w (M : Action AddCommGrpCat.{w} G) ⦃X Y : C⦄ (g : X ⟶ Y)
    (x : Φ.fiber.obj X) :
    (Φ.equivariantPresheaf act M).map g.op ≫ Φ.evalEquivariantMaps act M X x =
      Φ.evalEquivariantMaps act M Y (Φ.fiber.map g x) :=
  rfl

/-- The counit of the adjunction: `[X, x, f] ↦ f x`. -/
noncomputable def fromEquivariantSheaf (M : Action AddCommGrpCat.{w} G) :
    (Φ.sheafFiberAction act).obj (Φ.equivariantSheaf act M) ⟶ M where
  hom := Φ.presheafFiberDesc (Φ.evalEquivariantMaps act M) (Φ.evalEquivariantMaps_w act M)
  comm σ := by
    refine Φ.presheafFiber_hom_ext fun X x ↦ ?_
    change Φ.toPresheafFiber X x _ ≫ Φ.presheafFiberAct act _ σ ≫
        Φ.presheafFiberDesc (Φ.evalEquivariantMaps act M) (Φ.evalEquivariantMaps_w act M) =
      Φ.toPresheafFiber X x _ ≫
        Φ.presheafFiberDesc (Φ.evalEquivariantMaps act M) (Φ.evalEquivariantMaps_w act M) ≫
          (M.ρ σ).asHom
    rw [toPresheafFiber_presheafFiberAct_assoc,
      Φ.toPresheafFiber_presheafFiberDesc _ (Φ.evalEquivariantMaps_w act M),
      Φ.toPresheafFiber_presheafFiberDesc_assoc _ (Φ.evalEquivariantMaps_w act M)]
    exact AddCommGrpCat.ext fun f ↦ f.2 σ x

@[reassoc (attr := simp)]
lemma toPresheafFiber_fromEquivariantSheaf_hom (M : Action AddCommGrpCat.{w} G) (X : C)
    (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x (Φ.equivariantSheaf act M).obj ≫ (Φ.fromEquivariantSheaf act M).hom =
      Φ.evalEquivariantMaps act M X x :=
  Φ.toPresheafFiber_presheafFiberDesc (Φ.evalEquivariantMaps act M)
    (Φ.evalEquivariantMaps_w act M) X x

@[simp]
lemma toPresheafFiber_fromEquivariantSheaf_hom_apply (M : Action AddCommGrpCat.{w} G) (X : C)
    (x : Φ.fiber.obj X) (f : (Φ.equivariantPresheaf act M).obj (op X)) :
    (Φ.fromEquivariantSheaf act M).hom.hom
      (Φ.toPresheafFiber X x (Φ.equivariantPresheaf act M) f) = f.1 x :=
  congr($(Φ.toPresheafFiber_fromEquivariantSheaf_hom act M X x).hom f)

/-- The fibre functor with its `G`-action is left adjoint to the sheaf of equivariant maps. -/
noncomputable def sheafFiberActionAdjunction :
    Φ.sheafFiberAction act ⊣ Φ.equivariantSheafFunctor act :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app F := Φ.toEquivariantSheaf act F
          naturality {F F'} g := by
            ext X : 3
            exact AddCommGrpCat.ext fun t ↦ Subtype.ext (funext fun x ↦
              (Φ.toPresheafFiber_naturality_apply g.hom X.unop x t).symm) }
      counit :=
        { app M := Φ.fromEquivariantSheaf act M
          naturality {M N} φ := by
            ext : 1
            refine Φ.presheafFiber_hom_ext fun X x ↦ ?_
            change Φ.toPresheafFiber X x _ ≫ Φ.presheafFiber.map _ ≫ _ =
              Φ.toPresheafFiber X x _ ≫ _ ≫ φ.hom
            rw [toPresheafFiber_naturality_assoc]
            refine AddCommGrpCat.ext fun f ↦ ?_
            simp only [ConcreteCategory.comp_apply]
            erw [toPresheafFiber_fromEquivariantSheaf_hom_apply,
              toPresheafFiber_fromEquivariantSheaf_hom_apply]
            rfl }
      left_triangle := by
        ext F : 3
        refine Φ.presheafFiber_hom_ext fun X x ↦ ?_
        change Φ.toPresheafFiber X x _ ≫ Φ.presheafFiber.map _ ≫ _ = Φ.toPresheafFiber X x _ ≫ 𝟙 _
        rw [toPresheafFiber_naturality_assoc, Category.comp_id]
        exact AddCommGrpCat.ext fun t ↦ toPresheafFiber_fromEquivariantSheaf_hom_apply _ _ _ _ _ _
      right_triangle := by
        refine NatTrans.ext (funext fun M ↦ Sheaf.hom_ext (NatTrans.ext (funext fun X ↦
          AddCommGrpCat.ext fun f ↦ Subtype.ext (funext fun x ↦ ?_))))
        exact toPresheafFiber_fromEquivariantSheaf_hom_apply _ _ _ _ _ _ }

section constant

/-- The action of `σ` on fibres of presheaves is natural. -/
@[reassoc]
lemma presheafFiber_map_presheafFiberAct {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (f : P ⟶ Q) (σ : G) :
    Φ.presheafFiber.map f ≫ Φ.presheafFiberAct act Q σ =
      Φ.presheafFiberAct act P σ ≫ Φ.presheafFiber.map f :=
  Φ.presheafFiber_hom_ext fun X x ↦ by
    rw [toPresheafFiber_naturality_assoc, toPresheafFiber_presheafFiberAct,
      toPresheafFiber_presheafFiberAct_assoc, toPresheafFiber_naturality]

/-- `G` acts trivially on the fibre of a constant presheaf. -/
lemma presheafFiberAct_const (A : AddCommGrpCat.{w}) (σ : G) :
    Φ.presheafFiberAct act ((Functor.const Cᵒᵖ).obj A) σ = 𝟙 _ :=
  Φ.presheafFiber_hom_ext fun X x ↦ by
    rw [toPresheafFiber_presheafFiberAct, Category.comp_id,
      ← cancel_mono (Φ.presheafFiberConstIso A).hom, toPresheafFiber_presheafFiberConstIso_hom,
      toPresheafFiber_presheafFiberConstIso_hom]

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [LocallySmall.{w} C]

/-- `G` acts trivially on the fibre of a constant sheaf. -/
lemma sheafFiberAction_constantSheaf_ρ (A : AddCommGrpCat.{w}) (σ : G) :
    ((Φ.sheafFiberAction act).obj ((constantSheaf J AddCommGrpCat.{w}).obj A)).ρ σ = .of (𝟙 _) := by
  apply End.ext
  change Φ.presheafFiberAct act (CategoryTheory.sheafify J ((Functor.const Cᵒᵖ).obj A)) σ = 𝟙 _
  rw [← cancel_epi (Φ.presheafFiber.map (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj A))),
    presheafFiber_map_presheafFiberAct, presheafFiberAct_const, Category.id_comp,
    Category.comp_id]

/-- The fibre of the constant sheaf with value `A`, with its action of `G`, is `A` with the
trivial action. -/
noncomputable def sheafFiberActionConstantSheafIso (A : AddCommGrpCat.{w}) :
    (Φ.sheafFiberAction act).obj ((constantSheaf J AddCommGrpCat.{w}).obj A) ≅
      Action.trivial G A :=
  Action.mkIso (Φ.sheafFiberConstantSheafIso A) fun σ ↦ by
    rw [sheafFiberAction_constantSheaf_ρ]
    rfl

end constant

end CategoryTheory.GrothendieckTopology.Point
