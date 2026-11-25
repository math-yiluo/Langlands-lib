/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Module objects over a monoid object acting on its own category

For a monoid object `A` of a monoidal category `C`, acting on `C` through the tensor product,
this file records the action `A ⊗ X ⟶ X` of an `A`-module object `X` and its axioms in terms of
the tensor product (`CategoryTheory.Mod.act`), and the basic properties of the forgetful functor
`Mod.forget A : Mod C A ⥤ C`: it is faithful and reflects isomorphisms.

It also provides the image of a module object under a lax monoidal functor
(`CategoryTheory.Functor.mapMod`), which mathlib lists as a TODO in
`Mathlib.CategoryTheory.Monoidal.Mon`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

namespace Mod

variable {A : C} [MonObj A]

/-- The action `A ⊗ X ⟶ X` of a monoid object `A` on an `A`-module object `X` of `C`. -/
abbrev act (X : C) [ModObj A X] : A ⊗ X ⟶ X :=
  γ[A, X]

@[reassoc (attr := simp)]
lemma one_act (X : C) [ModObj A X] : η[A] ▷ X ≫ act X = (λ_ X).hom :=
  ModObj.one_smul (M := A) X

@[reassoc (attr := simp)]
lemma mul_act (X : C) [ModObj A X] :
    μ[A] ▷ X ≫ act X = (α_ A A X).hom ≫ A ◁ act X ≫ act X :=
  ModObj.mul_smul (M := A) X

@[reassoc]
lemma act_comp {X Y : C} [ModObj A X] [ModObj A Y] (f : X ⟶ Y) [IsModHom A f] :
    act X ≫ f = A ◁ f ≫ act Y :=
  IsModHom.smul_hom

@[reassoc (attr := simp)]
lemma act_hom {M N : Mod C A} (f : M ⟶ N) : act M.X ≫ f.hom = A ◁ f.hom ≫ act N.X :=
  IsModHom.smul_hom

variable (A) in
/-- An `A`-module structure on an object of `C`, from an action `A ⊗ X ⟶ X` satisfying the
axioms, stated in terms of the tensor product. -/
@[implicit_reducible]
def _root_.CategoryTheory.ModObj.mk' {X : C} (smul : A ⊗ X ⟶ X)
    (one_smul : η[A] ▷ X ≫ smul = (λ_ X).hom)
    (mul_smul : μ[A] ▷ X ≫ smul = (α_ A A X).hom ≫ A ◁ smul ≫ smul) : ModObj A X where
  smul := smul
  one_smul := one_smul
  mul_smul := mul_smul

lemma isModHom_of_act {X Y : C} [ModObj A X] [ModObj A Y] (f : X ⟶ Y)
    (h : act X ≫ f = A ◁ f ≫ act Y) : IsModHom A f :=
  ⟨h⟩

/-- A morphism of `A`-modules from a morphism commuting with the actions. -/
@[simps]
def homMk {M N : Mod C A} (f : M.X ⟶ N.X) (h : act M.X ≫ f = A ◁ f ≫ act N.X) : M ⟶ N :=
  letI := isModHom_of_act f h
  ⟨f⟩

instance : (forget (D := C) A).Faithful where
  map_injective h := Mod.hom_ext _ _ h

instance {M N : Mod C A} (f : M ⟶ N) [IsIso f] : IsIso f.hom :=
  inferInstanceAs (IsIso ((forget A).map f))

instance : (forget (D := C) A).ReflectsIsomorphisms where
  reflects {M N} f _ := by
    have : IsIso f.hom := ‹IsIso ((forget A).map f)›
    let e : M.X ≅ N.X := asIso f.hom
    have : IsModHom A e.hom := inferInstanceAs (IsModHom A f.hom)
    exact ⟨⟨⟨e.inv⟩, Mod.hom_ext _ _ e.hom_inv_id, Mod.hom_ext _ _ e.inv_hom_id⟩⟩

/-- An isomorphism of `A`-modules from an isomorphism commuting with the actions. -/
@[simps!]
def isoMk {M N : Mod C A} (e : M.X ≅ N.X) (h : act M.X ≫ e.hom = A ◁ e.hom ≫ act N.X) :
    M ≅ N where
  hom := homMk e.hom h
  inv := homMk e.inv (by
    rw [Iso.comp_inv_eq, Category.assoc, h, ← whiskerLeft_comp_assoc, Iso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp])
  hom_inv_id := Mod.hom_ext _ _ e.hom_inv_id
  inv_hom_id := Mod.hom_ext _ _ e.inv_hom_id

/-- The linear map `A ⟶ M` sending `1` to `x`. -/
def regularLift (M : Mod C A) (x : 𝟙_ C ⟶ M.X) : regular A ⟶ M :=
  homMk ((ρ_ A).inv ≫ A ◁ x ≫ act M.X) (by
    change (MonObj.mul : A ⊗ A ⟶ A) ≫ (ρ_ A).inv ≫ A ◁ x ≫ act M.X =
      A ◁ ((ρ_ A).inv ≫ A ◁ x ≫ act M.X) ≫ act M.X
    rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc]
    erw [mul_act]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    monoidal)

lemma one_comp_regularLift (M : Mod C A) (x : 𝟙_ C ⟶ M.X) :
    (MonObj.one : 𝟙_ C ⟶ A) ≫ (regularLift M x).hom = x := by
  change (MonObj.one : 𝟙_ C ⟶ A) ≫ (ρ_ A).inv ≫ A ◁ x ≫ act M.X = x
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc]
  erw [one_act]
  monoidal

lemma regular_hom_ext {M : Mod C A} {f g : regular A ⟶ M}
    (h : (MonObj.one : 𝟙_ C ⟶ A) ≫ f.hom = (MonObj.one : 𝟙_ C ⟶ A) ≫ g.hom) :
    f = g := by
  have key (f : regular A ⟶ M) : f = regularLift M ((MonObj.one : 𝟙_ C ⟶ A) ≫ f.hom) := by
    refine Mod.hom_ext _ _ ?_
    change f.hom = (ρ_ A).inv ≫ A ◁ ((MonObj.one : 𝟙_ C ⟶ A) ≫ f.hom) ≫ act M.X
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    erw [← IsModHom.smul_hom (A := A) (f := f.hom)]
    change f.hom = (ρ_ A).inv ≫ A ◁ (MonObj.one : 𝟙_ C ⟶ A) ≫ (MonObj.mul : A ⊗ A ⟶ A) ≫ f.hom
    rw [MonObj.mul_one_assoc, Iso.inv_hom_id_assoc]
  rw [key f, key g, h]

end Mod

namespace Functor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]

open LaxMonoidal _root_.CategoryTheory.Mod

open scoped Obj

variable {A : C} [MonObj A]

/-- The image of an `A`-module object under a lax monoidal functor `F` is an `F A`-module
object, with the action `F A ⊗ F X ⟶ F (A ⊗ X) ⟶ F X`. -/
@[implicit_reducible]
def modObjObj (X : C) [ModObj A X] : ModObj (F.obj A) (F.obj X) :=
  .mk' _ (LaxMonoidal.μ F A X ≫ F.map (act X))
    (by
      rw [obj.η_def, comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
        ← F.map_comp, one_act, left_unitality])
    (by
      rw [obj.μ_def, comp_whiskerRight, Category.assoc, μ_natural_left_assoc, ← F.map_comp,
        mul_act, F.map_comp, F.map_comp]
      simp only [associativity_assoc, MonoidalCategory.whiskerLeft_comp, Category.assoc,
        μ_natural_right_assoc])

variable (A) in
/-- A lax monoidal functor `F : C ⥤ D` takes `A`-module objects to `F A`-module objects. -/
@[simps]
def mapMod : Mod C A ⥤ Mod D (F.obj A) where
  obj M :=
    letI := F.modObjObj (A := A) M.X
    ⟨F.obj M.X⟩
  map {M N} f :=
    letI := F.modObjObj (A := A) M.X
    letI := F.modObjObj (A := A) N.X
    homMk (F.map f.hom) (by
      change (LaxMonoidal.μ F A M.X ≫ F.map (act M.X)) ≫ _ =
        _ ≫ LaxMonoidal.μ F A N.X ≫ F.map (act N.X)
      rw [Category.assoc, ← F.map_comp, act_hom, F.map_comp, μ_natural_right_assoc])

end Functor

end CategoryTheory

namespace CategoryTheory

namespace Mod

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

lemma act_comap_obj {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f] (M : Mod C B) :
    act ((comap f).obj M).X = f ▷ M.X ≫ act M.X :=
  rfl

end Mod

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

open _root_.CategoryTheory.Mod

open scoped Obj

lemma act_mapMod_obj (F : C ⥤ D) [F.LaxMonoidal] {A : C} [MonObj A] (M : Mod C A) :
    act ((F.mapMod A).obj M).X = LaxMonoidal.μ F A M.X ≫ F.map (act M.X) :=
  rfl

end Functor

namespace NatTrans

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

open scoped Obj

/-- The components of a monoidal natural transformation at monoid objects are monoid
morphisms. -/
instance isMonHom_app {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (α : F ⟶ G)
    [NatTrans.IsMonoidal α] (X : C) [MonObj X] : IsMonHom (α.app X) :=
  (Functor.mapMonNatTrans α |>.app (Mon.mk X)).isMonHom_hom

end NatTrans

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

open scoped Obj

open _root_.CategoryTheory.Mod

/-- A monoidal natural transformation `α : F ⟶ G` of lax monoidal functors induces, for each
monoid `A`, a natural transformation of the induced functors on `A`-modules, the `G A`-modules
being viewed as `F A`-modules along `α_A`. -/
@[simps]
def mapModNatTrans {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (α : F ⟶ G)
    [NatTrans.IsMonoidal α] (A : C) [MonObj A] :
    F.mapMod A ⟶ G.mapMod A ⋙ comap (α.app A) where
  app M := homMk (M := (F.mapMod A).obj M) (N := (comap (α.app A)).obj ((G.mapMod A).obj M))
    (α.app M.X) (by
      rw [act_comap_obj, act_mapMod_obj, act_mapMod_obj, Category.assoc, α.naturality,
        NatTrans.IsMonoidal.tensor_assoc, tensorHom_def', Category.assoc]
      rfl)
  naturality _ _ f := Mod.hom_ext _ _ (α.naturality f.hom)

/-- A monoidal natural isomorphism of lax monoidal functors induces an isomorphism of the
induced functors on modules. -/
@[simps!]
def mapModNatIso {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] (α : F ≅ G)
    [NatTrans.IsMonoidal α.hom] (A : C) [MonObj A] :
    F.mapMod A ≅ G.mapMod A ⋙ comap (α.hom.app A) :=
  NatIso.ofComponents (fun M ↦ isoMk (M := (F.mapMod A).obj M)
      (N := (comap (α.hom.app A)).obj ((G.mapMod A).obj M)) (α.app M.X)
      (act_hom ((mapModNatTrans α.hom A).app M)))
    fun f ↦ Mod.hom_ext _ _ (α.hom.naturality f.hom)

end Functor

instance IsMonHom.inv {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] {M N : C}
    [MonObj M] [MonObj N] (f : M ⟶ N) [IsIso f] [IsMonHom f] : IsMonHom (inv f) :=
  inferInstanceAs (IsMonHom (asIso f).inv)

namespace Adjunction

open Functor.LaxMonoidal Functor.OplaxMonoidal _root_.CategoryTheory.Mod

open scoped Obj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]
  {A : C} {B : D} [MonObj A] [MonObj B] (φ : A ⟶ G.obj B) [IsMonHom φ]
  [IsIso ((adj.homEquiv _ _).symm φ)] [IsMonHom ((adj.homEquiv _ _).symm φ)]

/-- The left adjoint `M ↦ F M` on module objects, the `F A`-module `F M` viewed as a `B`-module
along the inverse of the adjoint `F A ⟶ B` of `φ : A ⟶ G B`. -/
noncomputable def modLeft : Mod C A ⥤ Mod D B :=
  F.mapMod A ⋙ comap (inv ((adj.homEquiv _ _).symm φ))

/-- The right adjoint `N ↦ G N` on module objects, the `G B`-module `G N` viewed as an
`A`-module along `φ : A ⟶ G B`. -/
@[nolint unusedArguments]
noncomputable def modRight (_adj : F ⊣ G) (φ : A ⟶ G.obj B) [IsMonHom φ] : Mod D B ⥤ Mod C A :=
  G.mapMod B ⋙ comap φ

omit [G.LaxMonoidal] [adj.IsMonoidal] [IsMonHom φ] in
variable {adj φ} in
/-- A morphism `F M ⟶ N` is `B`-linear iff `F (A ⊗ M) ⟶ F M ⟶ N` agrees with
`F (A ⊗ M) ⟶ F A ⊗ F M ⟶ B ⊗ N ⟶ N`. -/
lemma modLeft_linear_iff {M : Mod C A} {N : Mod D B} (f : F.obj M.X ⟶ N.X) :
    act ((adj.modLeft φ).obj M).X ≫ f = B ◁ f ≫ act N.X ↔
      F.map (act M.X) ≫ f = δ F A M.X ≫ ((adj.homEquiv _ _).symm φ ⊗ₘ f) ≫ act N.X := by
  set ψ := (adj.homEquiv _ _).symm φ
  change (inv ψ ▷ F.obj M.X ≫ Functor.LaxMonoidal.μ F A M.X ≫ F.map (act M.X)) ≫ f = _ ↔ _
  constructor
  · intro h
    have h' := congrArg (fun k ↦ δ F A M.X ≫ ψ ▷ F.obj M.X ≫ k) h
    simpa only [Category.assoc, ← comp_whiskerRight_assoc, IsIso.hom_inv_id, id_whiskerRight,
      Category.id_comp, Functor.Monoidal.δ_μ_assoc, tensorHom_def] using h'
  · intro h
    rw [Category.assoc, Category.assoc, h, Functor.Monoidal.μ_δ_assoc, tensorHom_def]
    simp only [Category.assoc, ← comp_whiskerRight_assoc, IsIso.inv_hom_id, id_whiskerRight,
      Category.id_comp]

omit [IsIso ((adj.homEquiv A B).symm φ)] [IsMonHom ((adj.homEquiv A B).symm φ)] in
variable {adj φ} in
/-- A morphism `M ⟶ G N` is `A`-linear iff its adjoint `F M ⟶ N` satisfies the condition of
`CategoryTheory.Adjunction.modLeft_linear_iff`. -/
lemma modRight_linear_iff {M : Mod C A} {N : Mod D B} (g : M.X ⟶ G.obj N.X) :
    act M.X ≫ g = A ◁ g ≫ act ((adj.modRight φ).obj N).X ↔
      F.map (act M.X) ≫ (adj.homEquiv _ _).symm g =
        δ F A M.X ≫ ((adj.homEquiv _ _).symm φ ⊗ₘ (adj.homEquiv _ _).symm g) ≫ act N.X := by
  change act M.X ≫ g = A ◁ g ≫ φ ▷ G.obj N.X ≫ Functor.LaxMonoidal.μ G B N.X ≫ G.map (act N.X) ↔ _
  rw [← (adj.homEquiv _ _).symm.injective.eq_iff, adj.homEquiv_naturality_left_symm]
  have key : (adj.homEquiv _ _).symm (A ◁ g ≫ φ ▷ G.obj N.X ≫ Functor.LaxMonoidal.μ G B N.X ≫
      G.map (act N.X)) = δ F A M.X ≫ ((adj.homEquiv _ _).symm φ ⊗ₘ
        (adj.homEquiv _ _).symm g) ≫ act N.X := by
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      Adjunction.counit_naturality, Adjunction.map_μ_comp_counit_app_tensor_assoc]
    rw [← δ_natural_left_assoc, ← δ_natural_right_assoc]
    simp only [tensorHom_def, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      whisker_exchange_assoc]
  rw [key]

/-- **A monoidal adjunction lifts to module objects**: for a monoidal adjunction `F ⊣ G` with `F`
strong monoidal and a monoid morphism `φ : A ⟶ G B` whose adjoint `F A ⟶ B` is invertible,
`F` and `G` induce an adjunction between `A`-modules and `B`-modules. -/
noncomputable def modAdjunction : adj.modLeft φ ⊣ adj.modRight φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N :=
        { toFun f := homMk (M := M) (N := (adj.modRight φ).obj N) (adj.homEquiv _ _ f.hom)
            ((modRight_linear_iff _).2 (by
              rw [Equiv.symm_apply_apply]
              exact (modLeft_linear_iff _).1 (act_hom f)))
          invFun g := homMk (M := (adj.modLeft φ).obj M) (N := N) ((adj.homEquiv _ _).symm g.hom)
            ((modLeft_linear_iff _).2 ((modRight_linear_iff _).1 (act_hom g)))
          left_inv f := Mod.hom_ext _ _ (Equiv.symm_apply_apply _ _)
          right_inv g := Mod.hom_ext _ _ (Equiv.apply_symm_apply _ _) }
      homEquiv_naturality_left_symm f g :=
        Mod.hom_ext _ _ (adj.homEquiv_naturality_left_symm f.hom g.hom)
      homEquiv_naturality_right f g :=
        Mod.hom_ext _ _ (adj.homEquiv_naturality_right f.hom g.hom) }

lemma modAdjunction_homEquiv_apply_hom {M : Mod C A} {N : Mod D B}
    (f : (adj.modLeft φ).obj M ⟶ N) :
    ((adj.modAdjunction φ).homEquiv M N f).hom = adj.homEquiv _ _ f.hom := by
  simp [modAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

end Adjunction

end CategoryTheory

namespace CategoryTheory

namespace Mod

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- Restriction of scalars along a composite is the composite of the restrictions. -/
@[simps!]
def comapComp {A B B' : C} [MonObj A] [MonObj B] [MonObj B'] (f : A ⟶ B) (g : B ⟶ B')
    [IsMonHom f] [IsMonHom g] : comap (D := C) (f ≫ g) ≅ comap g ⋙ comap f :=
  NatIso.ofComponents (fun M ↦ isoMk (M := (comap (f ≫ g)).obj M)
      (N := (comap f).obj ((comap g).obj M)) (Iso.refl _) (by
        simp only [act_comap_obj, Iso.refl_hom, Category.comp_id,
          MonoidalCategory.whiskerLeft_id, Category.id_comp, comp_whiskerRight,
          Category.assoc]
        rfl))
    fun _ ↦ Mod.hom_ext _ _ (by simp)

/-- Restriction of scalars along the identity is the identity. -/
@[simps!]
def comapId (A : C) [MonObj A] : comap (D := C) (𝟙 A) ≅ 𝟭 (Mod C A) :=
  NatIso.ofComponents (fun M ↦ isoMk (M := (comap (𝟙 A)).obj M) (N := M) (Iso.refl _) (by
      simp only [act_comap_obj, Iso.refl_hom, Category.comp_id, MonoidalCategory.whiskerLeft_id,
        Category.id_comp, id_whiskerRight]))
    fun _ ↦ Mod.hom_ext _ _ (by simp)

/-- Restrictions of scalars along equal morphisms are isomorphic. -/
def comapCongr {A B : C} [MonObj A] [MonObj B] {f g : A ⟶ B} [IsMonHom f] [IsMonHom g]
    (h : f = g) : comap (D := C) f ≅ comap g :=
  NatIso.ofComponents (fun M ↦ isoMk (M := (comap f).obj M) (N := (comap g).obj M) (Iso.refl _)
      (by subst h; simp))
    fun _ ↦ Mod.hom_ext _ _ (by simp)

@[simp]
lemma comapCongr_hom_app_hom {A B : C} [MonObj A] [MonObj B] {f g : A ⟶ B} [IsMonHom f]
    [IsMonHom g] (h : f = g) (M : Mod C B) :
    ((comapCongr h).hom.app M).hom = 𝟙 M.X :=
  rfl

end Mod

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

open scoped Obj

open _root_.CategoryTheory.Mod

end Functor

end CategoryTheory

namespace CategoryTheory.Functor

open _root_.CategoryTheory.Mod

open scoped Obj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- Linearity of the components of a monoidal natural transformation `F ⋙ G ⟶ H` between the
modules obtained by restricting scalars along monoid morphisms `ψ' ≫ G ψ` and `φ` compatible with
it. -/
lemma act_comp_app_of_isMonoidal {E : Type*} [Category E] [MonoidalCategory E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (e : F ⋙ G ⟶ H) [NatTrans.IsMonoidal e] {A : C} {B : D} {B' : E} [MonObj A] [MonObj B]
    [MonObj B'] (ψ : B ⟶ F.obj A) (ψ' : B' ⟶ G.obj B) (φ : B' ⟶ H.obj A) [IsMonHom ψ]
    [IsMonHom ψ'] [IsMonHom φ] (h : ψ' ≫ G.map ψ ≫ e.app A = φ) (M : Mod C A) :
    act ((comap ψ').obj ((G.mapMod B).obj ((comap ψ).obj ((F.mapMod A).obj M)))).X ≫ e.app M.X =
      B' ◁ e.app M.X ≫ act ((comap φ).obj ((H.mapMod A).obj M)).X := by
  subst h
  have hm := NatTrans.IsMonoidal.tensor (τ := e) A M.X
  rw [LaxMonoidal.comp_μ] at hm
  simp only [act_comap_obj, act_mapMod_obj, Functor.map_comp, Category.assoc]
  rw [← Functor.comp_map, e.naturality]
  simp only [comp_whiskerRight, Category.assoc]
  erw [← LaxMonoidal.μ_natural_left_assoc, reassoc_of% hm]
  rw [tensorHom_def']
  simp only [Category.assoc, ← whisker_exchange_assoc]
  rfl

/-- Linearity of the components of a monoidal natural transformation `F ⟶ 𝟭` between the modules
obtained by restricting scalars along monoid morphisms `ψ` and `φ` compatible with it. -/
lemma act_comp_app_of_isMonoidal_id {F : C ⥤ C} [F.LaxMonoidal] (e : F ⟶ 𝟭 C)
    [NatTrans.IsMonoidal e] {A B : C} [MonObj A] [MonObj B] (ψ : B ⟶ F.obj A) (φ : B ⟶ A)
    [IsMonHom ψ] [IsMonHom φ] (h : ψ ≫ e.app A = φ) (M : Mod C A) :
    act ((comap ψ).obj ((F.mapMod A).obj M)).X ≫ e.app M.X =
      B ◁ e.app M.X ≫ act ((comap φ).obj M).X := by
  subst h
  have hm := NatTrans.IsMonoidal.tensor (τ := e) A M.X
  rw [LaxMonoidal.id_μ, Category.comp_id] at hm
  simp only [act_comap_obj, act_mapMod_obj, Category.assoc]
  erw [e.naturality]
  rw [reassoc_of% hm, comp_whiskerRight, Category.assoc, tensorHom_def']
  erw [Category.assoc, ← whisker_exchange_assoc]
  rfl

/-- A monoidal natural isomorphism `κ : F ≅ 𝟭` identifies the functor `F.mapMod A` with the
restriction of scalars along a monoid morphism `α : F A ⟶ A` agreeing with `κ` at `A`: the
component at `M` is `κ_M : F M ≅ M`. -/
@[simps!]
def mapModIsoComapOfIsoId {F : C ⥤ C} [F.LaxMonoidal] (κ : F ≅ 𝟭 C) [NatTrans.IsMonoidal κ.hom]
    (A : C) [MonObj A] (α : F.obj A ⟶ A) [IsMonHom α] (hα : κ.hom.app A = α) :
    F.mapMod A ≅ comap α :=
  NatIso.ofComponents (fun M ↦ isoMk (M := (F.mapMod A).obj M) (N := (comap α).obj M)
      (κ.app M.X) (by
        have h := act_comp_app_of_isMonoidal_id κ.hom (𝟙 _) α (by rw [Category.id_comp, hα]) M
        simp only [act_comap_obj, id_whiskerRight, Category.id_comp] at h
        exact h))
    fun f ↦ Mod.hom_ext _ _ (κ.hom.naturality f.hom)

end CategoryTheory.Functor

namespace CategoryTheory.Mod

open scoped Obj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- A monoid isomorphism `φ : M ≅ B` identifies `M`, as a `B`-module along `φ⁻¹`, with the
regular `B`-module. -/
@[simps!]
noncomputable def regularIsoOfIsIso {M B : C} [MonObj M] [MonObj B] (φ : M ⟶ B) [IsIso φ]
    [IsMonHom φ] :
    (comap (D := C) (inv φ)).obj (regular M) ≅ regular B :=
  letI : IsMonHom (inv φ) := inferInstance
  isoMk (asIso φ) (by
    change (inv φ ▷ M ≫ μ[M]) ≫ φ = B ◁ φ ≫ μ[B]
    rw [Category.assoc, IsMonHom.mul_hom, tensorHom_def, Category.assoc,
      ← comp_whiskerRight_assoc, IsIso.inv_hom_id, id_whiskerRight, Category.id_comp])

end CategoryTheory.Mod

namespace CategoryTheory.Adjunction

open scoped Obj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]
  {A : C} {B : D} [MonObj A] [MonObj B] (φ : A ⟶ G.obj B) [IsMonHom φ]
  [IsIso ((adj.homEquiv _ _).symm φ)] [IsMonHom ((adj.homEquiv _ _).symm φ)]

lemma modAdjunction_homEquiv_symm_apply_hom {M : Mod C A} {N : Mod D B}
    (g : M ⟶ (adj.modRight φ).obj N) :
    (((adj.modAdjunction φ).homEquiv M N).symm g).hom = (adj.homEquiv _ _).symm g.hom := by
  simp [modAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

lemma modAdjunction_counit_app_hom (N : Mod D B) :
    ((adj.modAdjunction φ).counit.app N).hom = adj.counit.app N.X := by
  rw [← Adjunction.homEquiv_symm_id, modAdjunction_homEquiv_symm_apply_hom]
  exact Adjunction.homEquiv_symm_id _ _

lemma modAdjunction_unit_app_hom (M : Mod C A) :
    ((adj.modAdjunction φ).unit.app M).hom = adj.unit.app M.X := by
  rw [← Adjunction.homEquiv_id, modAdjunction_homEquiv_apply_hom]
  exact Adjunction.homEquiv_id _ _

end CategoryTheory.Adjunction
