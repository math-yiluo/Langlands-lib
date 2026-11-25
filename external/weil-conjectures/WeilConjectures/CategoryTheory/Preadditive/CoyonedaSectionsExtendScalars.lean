/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.NumberTheory.NumberField.House

/-!
# Sections over an object commute with extension of scalars

Let `X₁` be an object of a preadditive category `C₁` on which a commutative ring `A` acts
through `c₁ : A →+* (End X₁)ᵐᵒᵖ`, so that the sections `Hom(X₁, -)` are `A`-modules
(`CategoryTheory.coyonedaSections c₁`); similarly for `X₂`, `B` and `c₂` in `C₂`. Let
`f : A →+* B`, and let `H : C₁ ⥤ C₂` be an additive functor with `e : H X₁ ≅ X₂`, compatibly with
the actions. Then `m ↦ e⁻¹ ≫ H m` induces a natural `B`-linear comparison map
```
B ⊗_A Hom(X₁, M) ⟶ Hom(X₂, H M)
```
(`CategoryTheory.coyonedaSectionsExtendScalarsComparison`). It is an isomorphism at `M = X₁` as
soon as `A` acts on `X₁` through all its endomorphisms and `B ≅ End X₂`
(`CategoryTheory.isIso_coyonedaSectionsExtendScalarsComparison_app_self`).
-/

@[expose] public section

universe w

open CategoryTheory Limits

open scoped ChangeOfRings

namespace CategoryTheory

section Sections

variable {C : Type*} [Category.{w} C] [Preadditive C] {A : Type w} [Ring A] {X : C}

/-- The sections `Hom(X, -)` over an object `X` on which a ring `A` acts through
`c : A →+* (End X)ᵐᵒᵖ`, as `A`-modules. -/
noncomputable abbrev coyonedaSections (c : A →+* (End X)ᵐᵒᵖ) : C ⥤ ModuleCat.{w} A :=
  preadditiveCoyonedaObj X ⋙ ModuleCat.restrictScalars c

lemma coyonedaSections_smul (c : A →+* (End X)ᵐᵒᵖ) {M : C} (a : A)
    (m : (coyonedaSections c).obj M) : a • m = (c a).unop.asHom ≫ m :=
  rfl

end Sections

variable {C₁ C₂ : Type*} [Category.{w} C₁] [Category.{w} C₂] [Preadditive C₁] [Preadditive C₂]
  {A B : Type w} [CommRing A] [CommRing B] (f : A →+* B)
  {X₁ : C₁} {X₂ : C₂} (c₁ : A →+* (End X₁)ᵐᵒᵖ) (c₂ : B →+* (End X₂)ᵐᵒᵖ)
  (H : C₁ ⥤ C₂) [H.Additive] (e : H.obj X₁ ≅ X₂)
  (hH : ∀ a, e.inv ≫ H.map (c₁ a).unop.asHom = (c₂ (f a)).unop.asHom ≫ e.inv)

/-- The `A`-linear map `Hom(X₁, M) ⟶ Hom(X₂, H M)`, `m ↦ e⁻¹ ≫ H m`. -/
noncomputable def coyonedaSectionsMap :
    coyonedaSections c₁ ⟶ H ⋙ coyonedaSections c₂ ⋙ ModuleCat.restrictScalars f where
  app M := ModuleCat.ofHom (X := (coyonedaSections c₁).obj M)
    (Y := (H ⋙ coyonedaSections c₂ ⋙ ModuleCat.restrictScalars f).obj M)
    { toFun m := e.inv ≫ H.map m
      map_add' m m' := by
        rw [H.map_add, Preadditive.comp_add]
      map_smul' a m := by
        rw [coyonedaSections_smul, H.map_comp, ← Category.assoc, hH, Category.assoc]
        rfl }
  naturality M N g := by
    ext m
    exact (congrArg (e.inv ≫ ·) (H.map_comp m g)).trans (Category.assoc _ _ _).symm

lemma coyonedaSectionsMap_app_apply {M : C₁} (m : (coyonedaSections c₁).obj M) :
    (coyonedaSectionsMap f c₁ c₂ H e hH).app M m = e.inv ≫ H.map m :=
  rfl


/-- The comparison `B ⊗_A Hom(X₁, M) ⟶ Hom(X₂, H M)`, `b ⊗ m ↦ b • (e⁻¹ ≫ H m)`: the map adjoint
to `coyonedaSectionsMap`. -/
noncomputable def coyonedaSectionsExtendScalarsComparison :
    coyonedaSections c₁ ⋙ ModuleCat.extendScalars f ⟶ H ⋙ coyonedaSections c₂ where
  app M := ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm
    ((coyonedaSectionsMap f c₁ c₂ H e hH).app M)
  naturality M N g := by
    rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_left_symm,
      (coyonedaSectionsMap f c₁ c₂ H e hH).naturality]
    exact (ModuleCat.extendRestrictScalarsAdj f).homEquiv_naturality_right_symm _
      ((H ⋙ coyonedaSections c₂).map g)

lemma coyonedaSectionsExtendScalarsComparison_app_one_tmul {M : C₁}
    (m : (coyonedaSections c₁).obj M) :
    (coyonedaSectionsExtendScalarsComparison f c₁ c₂ H e hH).app M ((1 : B) ⊗ₜ[A, f] m) =
      e.inv ≫ H.map m :=
  congrArg (fun φ : (coyonedaSections c₁).obj M ⟶
      (ModuleCat.restrictScalars f).obj ((H ⋙ coyonedaSections c₂).obj M) ↦ φ m)
    (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).apply_symm_apply
      ((coyonedaSectionsMap f c₁ c₂ H e hH).app M))

/-- The comparison `B ⊗_A Hom(X₁, M) ⟶ Hom(X₂, H M)` is an isomorphism at `M = X₁` if every
endomorphism of `X₁` is the action of a scalar of `A` and if `B` acts bijectively on `X₂`:
both sides are then `B`. -/
lemma isIso_coyonedaSectionsExtendScalarsComparison_app_self
    (hc₁ : ∀ t : X₁ ⟶ X₁, ∃ a, (c₁ a).unop = .of (t))
    (hc₂ : Function.Bijective fun b ↦ (c₂ b).unop) :
    IsIso ((coyonedaSectionsExtendScalarsComparison f c₁ c₂ H e hH).app X₁) := by
  let α := (coyonedaSectionsExtendScalarsComparison f c₁ c₂ H e hH).app X₁
  let one : (ModuleCat.extendScalars f).obj ((coyonedaSections c₁).obj X₁) :=
    (1 : B) ⊗ₜ[A, f] (𝟙 X₁ : (coyonedaSections c₁).obj X₁)
  have hgen (z : (ModuleCat.extendScalars f).obj ((coyonedaSections c₁).obj X₁)) :
      ∃ b : B, z = b • one := by
    induction z using TensorProduct.inductionOn with
    | tmul b m =>
      obtain ⟨a, ha⟩ := hc₁ m
      let i : (coyonedaSections c₁).obj X₁ := 𝟙 X₁
      have hm : @Eq ((coyonedaSections c₁).obj X₁) m (a • i) :=
        (congrArg End.asHom ha).symm.trans (Category.comp_id _).symm
      refine ⟨a • b, ?_⟩
      rw [hm, ← TensorProduct.smul_tmul]
      exact congrArg (· ⊗ₜ[A, f] i) (@mul_one B _ (a • b)).symm
    | add z z' hz hz' =>
      obtain ⟨b, rfl⟩ := hz
      obtain ⟨b', rfl⟩ := hz'
      exact ⟨b + b', (add_smul _ _ _).symm⟩
  have hα (b : B) : α (b • one) = (c₂ b).unop.asHom ≫ e.inv := by
    rw [map_smul, coyonedaSectionsExtendScalarsComparison_app_one_tmul, H.map_id,
      Category.comp_id]
    rfl
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun z z' h ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨b, rfl⟩ := hgen z
    obtain ⟨b', rfl⟩ := hgen z'
    have h' : (c₂ b).unop.asHom ≫ e.inv = (c₂ b').unop.asHom ≫ e.inv :=
      (hα b).symm.trans (h.trans (hα b'))
    rw [hc₂.1 (End.ext ((cancel_mono e.inv).1 h'))]
  · obtain ⟨b, hb⟩ := hc₂.2 (End.of (y ≫ e.hom))
    refine ⟨b • one, ?_⟩
    rw [hα, Iso.comp_inv_eq]
    exact congrArg End.asHom hb

end CategoryTheory
