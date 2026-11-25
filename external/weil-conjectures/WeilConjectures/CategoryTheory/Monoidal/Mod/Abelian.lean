/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits

/-!
# Module objects in an abelian monoidal category

Let `C` be an abelian monoidal category whose tensor product is additive, and `A` a monoid object
of `C` such that `A ⊗ -` preserves colimits. Then the category `Mod C A` of `A`-module objects is
abelian, the forgetful functor `Mod.forget A` being faithful, exact and conservative; and if
`C` is a Grothendieck abelian category, so is `Mod C A`, with separator the free module
`A ⊗ S` on a separator `S` of `C`.

## Main results

- `CategoryTheory.Mod.instAbelian`: `Mod C A` is abelian.
- `CategoryTheory.Mod.free` and `CategoryTheory.Mod.freeForgetAdjunction`: the free module
  functor `X ↦ A ⊗ X`, left adjoint to the forgetful functor.
- `CategoryTheory.Mod.isGrothendieckAbelian`: `Mod C A` is Grothendieck abelian when `C` is.
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (A : C) [MonObj A]

section Free

/-- The free `A`-module structure on `A ⊗ X`, acting by multiplication on the first factor. -/
@[implicit_reducible]
def freeModObj (X : C) : ModObj A (A ⊗ X) :=
  .mk' A ((α_ A A X).inv ≫ μ ▷ X)
    (by rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, MonObj.one_mul,
      leftUnitor_tensor_hom])
    (by
      rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, MonObj.mul_assoc,
        MonoidalCategory.whiskerLeft_comp_assoc, associator_inv_naturality_middle_assoc]
      simp only [comp_whiskerRight]
      monoidal)

/-- The free `A`-module `A ⊗ X` on an object `X`, with the action given by multiplication. -/
@[simps!]
abbrev free : C ⥤ Mod C A where
  obj X :=
    letI := freeModObj A X
    ⟨A ⊗ X⟩
  map {X Y} f :=
    letI := freeModObj A X
    letI := freeModObj A Y
    homMk (M := ⟨A ⊗ X⟩) (N := ⟨A ⊗ Y⟩) (A ◁ f) (by
      change ((α_ A A X).inv ≫ μ ▷ X) ≫ A ◁ f = A ◁ A ◁ f ≫ (α_ A A Y).inv ≫ μ ▷ Y
      rw [Category.assoc, ← whisker_exchange, associator_inv_naturality_right_assoc])
  map_id X := Mod.hom_ext _ _ (MonoidalCategory.whiskerLeft_id _ _)
  map_comp f g := Mod.hom_ext _ _ (MonoidalCategory.whiskerLeft_comp _ _ _)

/-- The morphism of `A`-modules `A ⊗ X ⟶ M` extending a morphism `X ⟶ M`. -/
def freeDesc {X : C} {M : Mod C A} (g : X ⟶ M.X) : (free A).obj X ⟶ M :=
  letI := freeModObj A X
  homMk (M := ⟨A ⊗ X⟩) (A ◁ g ≫ act M.X) (by
    change ((α_ A A X).inv ≫ μ ▷ X) ≫ A ◁ g ≫ act M.X = A ◁ (A ◁ g ≫ act M.X) ≫ act M.X
    simp only [Category.assoc]
    rw [← whisker_exchange_assoc, mul_act, ← associator_inv_naturality_right_assoc,
      Iso.inv_hom_id_assoc, MonoidalCategory.whiskerLeft_comp_assoc])

@[simp]
lemma freeDesc_hom {X : C} {M : Mod C A} (g : X ⟶ M.X) : (freeDesc A g).hom = A ◁ g ≫ act M.X :=
  rfl

@[reassoc (attr := simp)]
lemma unit_freeDesc {X : C} {M : Mod C A} (g : X ⟶ M.X) :
    (λ_ X).inv ≫ η ▷ X ≫ (freeDesc A g).hom = g := by
  rw [freeDesc_hom, ← whisker_exchange_assoc, one_act, leftUnitor_naturality,
    Iso.inv_hom_id_assoc]

/-- The free `A`-module functor is left adjoint to the forgetful functor: a morphism of
`A`-modules `A ⊗ X ⟶ M` is determined by its restriction `X ⟶ A ⊗ X ⟶ M` along the unit. -/
def freeForgetAdjunction : free A ⊣ forget A :=
  Adjunction.mkOfHomEquiv
    { homEquiv X M :=
        { toFun f := (λ_ X).inv ≫ η ▷ X ≫ f.hom
          invFun g := freeDesc A g
          left_inv f := Mod.hom_ext _ _ (by
            have hf : ((α_ A A X).inv ≫ μ ▷ X) ≫ f.hom = A ◁ f.hom ≫ act M.X := act_hom f
            have hc : A ◁ (λ_ X).inv ≫ A ◁ η ▷ X ≫ (α_ A A X).inv ≫ μ ▷ X = 𝟙 (A ⊗ X) := by
              rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight, MonObj.mul_one]
              monoidal
            change (freeDesc A (M := M) ((λ_ X).inv ≫ η ▷ X ≫ f.hom)).hom = f.hom
            rw [freeDesc_hom, MonoidalCategory.whiskerLeft_comp_assoc,
              MonoidalCategory.whiskerLeft_comp_assoc, ← hf]
            simp only [← Category.assoc] at hc ⊢
            rw [hc, Category.id_comp])
          right_inv g := unit_freeDesc A g }
      homEquiv_naturality_left_symm {X X' M} f g := Mod.hom_ext _ _ (by
        change (freeDesc A (M := M) (f ≫ g)).hom = A ◁ f ≫ (freeDesc A (M := M) g).hom
        erw [freeDesc_hom, freeDesc_hom, MonoidalCategory.whiskerLeft_comp_assoc])
      homEquiv_naturality_right {X M M'} f g := by
        change (λ_ X).inv ≫ η ▷ X ≫ (f ≫ g).hom = ((λ_ X).inv ≫ η ▷ X ≫ f.hom) ≫ g.hom
        simp only [comp_hom', Category.assoc] }

end Free

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C]

section

variable {M N : Mod C A}

lemma isLinear_add {φ ψ : M.X ⟶ N.X} (hφ : act M.X ≫ φ = A ◁ φ ≫ act N.X)
    (hψ : act M.X ≫ ψ = A ◁ ψ ≫ act N.X) :
    act M.X ≫ (φ + ψ) = A ◁ (φ + ψ) ≫ act N.X := by
  rw [Preadditive.comp_add, hφ, hψ, MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp]

lemma isLinear_zsmul (n : ℤ) {φ : M.X ⟶ N.X} (hφ : act M.X ≫ φ = A ◁ φ ≫ act N.X) :
    act M.X ≫ (n • φ) = A ◁ (n • φ) ≫ act N.X := by
  rw [Preadditive.comp_zsmul, hφ, ← Preadditive.zsmul_comp]
  exact congrArg (· ≫ act N.X) (Functor.map_zsmul (tensorLeft A)).symm

lemma isLinear_nsmul (n : ℕ) {φ : M.X ⟶ N.X} (hφ : act M.X ≫ φ = A ◁ φ ≫ act N.X) :
    act M.X ≫ (n • φ) = A ◁ (n • φ) ≫ act N.X := by
  rw [Preadditive.comp_nsmul, hφ, ← Preadditive.nsmul_comp]
  exact congrArg (· ≫ act N.X) (Functor.map_nsmul (tensorLeft A)).symm

lemma isLinear_neg {φ : M.X ⟶ N.X} (hφ : act M.X ≫ φ = A ◁ φ ≫ act N.X) :
    act M.X ≫ (-φ) = A ◁ (-φ) ≫ act N.X := by
  simpa using isLinear_zsmul A (-1) hφ

instance : Zero (M ⟶ N) := ⟨homMk 0 (by simp)⟩
instance : Add (M ⟶ N) := ⟨fun f g ↦ homMk (f.hom + g.hom) (isLinear_add A (act_hom f) (act_hom g))⟩
instance : Neg (M ⟶ N) := ⟨fun f ↦ homMk (-f.hom) (isLinear_neg A (act_hom f))⟩
instance : Sub (M ⟶ N) := ⟨fun f g ↦ homMk (f.hom - g.hom) (by
  rw [sub_eq_add_neg]; exact isLinear_add A (act_hom f) (isLinear_neg A (act_hom g)))⟩
instance : SMul ℕ (M ⟶ N) := ⟨fun n f ↦ homMk (n • f.hom) (isLinear_nsmul A n (act_hom f))⟩
instance : SMul ℤ (M ⟶ N) := ⟨fun n f ↦ homMk (n • f.hom) (isLinear_zsmul A n (act_hom f))⟩

instance : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup (fun f : M ⟶ N ↦ f.hom) (fun _ _ h ↦ Mod.hom_ext _ _ h)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end

instance instPreadditive : Preadditive (Mod C A) where
  add_comp _ _ _ _ _ _ := Mod.hom_ext _ _ (Preadditive.add_comp _ _ _ _ _ _)
  comp_add _ _ _ _ _ _ := Mod.hom_ext _ _ (Preadditive.comp_add _ _ _ _ _ _)

@[simp]
lemma add_hom {M N : Mod C A} (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom :=
  rfl

@[simp]
lemma zero_hom {M N : Mod C A} : (0 : M ⟶ N).hom = 0 :=
  rfl

@[simp]
lemma neg_hom {M N : Mod C A} (f : M ⟶ N) : (-f).hom = -f.hom :=
  rfl

instance : (forget (D := C) A).Additive where

instance {A' : C} [MonObj A'] (f : A' ⟶ A) [IsMonHom f] : (comap (D := C) f).Additive where

open scoped Obj in
/-- The functor on modules induced by an additive lax monoidal functor is additive. -/
instance {D : Type*} [Category D] [MonoidalCategory D] [Preadditive D] [MonoidalPreadditive D]
    (F : C ⥤ D) [F.LaxMonoidal] [F.Additive] : (F.mapMod A).Additive where
  map_add := Mod.hom_ext _ _ F.map_add

end Preadditive

section Abelian

variable [Abelian C] [MonoidalPreadditive C] [PreservesFiniteColimits (tensorLeft A)]

instance : HasFiniteLimits (Mod C A) where
  out _ _ _ := inferInstance

instance : HasFiniteColimits (Mod C A) where
  out _ _ _ := inferInstance

instance : PreservesFiniteLimits (forget (D := C) A) where
  preservesFiniteLimits _ _ _ := inferInstance

instance : PreservesFiniteColimits (forget (D := C) A) where
  preservesFiniteColimits _ _ _ := inferInstance

instance {M N : Mod C A} (f : M ⟶ N) : IsIso (Abelian.coimageImageComparison f) := by
  have h := Abelian.PreservesCoimage.hom_coimageImageComparison (forget A) f
  have : IsIso ((forget A).map (Abelian.coimageImageComparison f)) := by
    rw [← Category.comp_id ((forget A).map _),
      ← (Abelian.PreservesImage.iso (forget A) f).hom_inv_id, ← Category.assoc, ← h]
    infer_instance
  exact isIso_of_reflects_iso _ (forget A)

/-- **Module objects in an abelian monoidal category form an abelian category**, when tensoring
with the monoid object is right exact. Kernels and cokernels are computed in `C`. -/
noncomputable instance instAbelian : Abelian (Mod C A) :=
  Abelian.ofCoimageImageComparisonIsIso

instance : ReflectsFiniteLimits (forget (D := C) A) where
  reflects _ _ _ := inferInstance

instance : ReflectsFiniteColimits (forget (D := C) A) where
  reflects _ _ _ := inferInstance

end Abelian

section Grothendieck

variable [Abelian C] [MonoidalPreadditive C]
  [∀ X : C, PreservesColimitsOfSize.{w, w} (tensorLeft X)]

instance : PreservesFiniteColimits (tensorLeft A) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- **Module objects in a Grothendieck abelian monoidal category** whose tensor product preserves
colimits in each variable form a Grothendieck abelian category. Filtered colimits are created by
the forgetful functor and are therefore exact, and the free module on a separator of `C` is a
separator. -/
theorem isGrothendieckAbelian [IsGrothendieckAbelian.{w} C] :
    IsGrothendieckAbelian.{w} (Mod C A) := by
  have : HasFilteredColimitsOfSize.{w, w} (Mod C A) := ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{w, w} (Mod C A) :=
    ⟨fun J _ _ ↦ HasExactColimitsOfShape.domain_of_functor J (forget A)⟩
  have : LocallySmall.{w} (Mod C A) := locallySmall_of_faithful (forget A)
  obtain ⟨S, hS⟩ := HasSeparator.hasSeparator (C := C)
  have : HasSeparator (Mod C A) := ⟨(free A).obj S, by
    rw [isSeparator_def] at hS ⊢
    intro M N f g hfg
    refine (forget A).map_injective (hS _ _ fun (s : S ⟶ M.X) ↦ ?_)
    have := congrArg (fun φ ↦ (λ_ S).inv ≫ η ▷ S ≫ φ.hom) (hfg (freeDesc A s))
    simp only [comp_hom', unit_freeDesc_assoc] at this
    exact this⟩
  exact {}

end Grothendieck

end CategoryTheory.Mod
