/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The underlying sheaf adjunction restricted to linear maps

Source: Stacks Project, Modules on Sites, Tags 03D1--03D3 and 03D7.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u uC vC
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings
namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Helpers

private noncomputable abbrev sheafHasBinaryProduct
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    (X Y : Sheaf J (Type u)) : HasBinaryProduct X Y := inferInstance

attribute [local instance] sheafHasBinaryProduct

private noncomputable abbrev ringBase
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private noncomputable abbrev moduleSets
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    (R : Sheaf J CommRingCat.{u}) :=
  toSheaf (ringBase R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})

private noncomputable def linearLift
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    {R : Sheaf J CommRingCat.{u}}
    {M N : SheafOfModules.{u} (ringBase R)}
    (α : (moduleSets R).obj M ⟶ (moduleSets R).obj N)
    (ha : ∀ W (x y : M.val.obj W), α.hom.app W (x + y) =
      (show N.val.obj W from α.hom.app W x) +
        (show N.val.obj W from α.hom.app W y))
    (hs : ∀ W (r : R.obj.obj W) (x : M.val.obj W), α.hom.app W (r • x) =
      r • (show N.val.obj W from α.hom.app W x)) : M ⟶ N where
  val :=
    { app W := ModuleCat.ofHom
        { toFun := α.hom.app W
          map_add' := ha W
          map_smul' := hs W }
      naturality := by
        intro X Y f
        ext x
        exact CategoryTheory.congr_fun (α.hom.naturality f) x }

private theorem linearLift_underlying
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    {R : Sheaf J CommRingCat.{u}}
    {M N : SheafOfModules.{u} (ringBase R)}
    (α : (moduleSets R).obj M ⟶ (moduleSets R).obj N) (ha hs) :
    (moduleSets R).map (linearLift α ha hs) = α := rfl


private noncomputable def sectionPair
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    (X Y : Sheaf J (Type u)) (W : Cᵒᵖ) (x : X.obj.obj W) (y : Y.obj.obj W) :
    (X ⨯ Y).obj.obj W :=
  (prod.lift (CartesianMonoidalCategory.fst X Y)
    (CartesianMonoidalCategory.snd X Y)).hom.app W (x, y)

private theorem sectionPair_fst
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    (X Y : Sheaf J (Type u)) (W : Cᵒᵖ) (x : X.obj.obj W) (y : Y.obj.obj W) :
    (prod.fst : X ⨯ Y ⟶ X).hom.app W (sectionPair X Y W x y) = x := by
  exact congrArg (fun f : X ⊗ Y ⟶ X ↦ f.hom.app W (x, y))
    (prod.lift_fst (CartesianMonoidalCategory.fst X Y)
      (CartesianMonoidalCategory.snd X Y))

private theorem sectionPair_snd
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    (X Y : Sheaf J (Type u)) (W : Cᵒᵖ) (x : X.obj.obj W) (y : Y.obj.obj W) :
    (prod.snd : X ⨯ Y ⟶ Y).hom.app W (sectionPair X Y W x y) = y := by
  exact congrArg (fun f : X ⊗ Y ⟶ Y ↦ f.hom.app W (x, y))
    (prod.lift_snd (CartesianMonoidalCategory.fst X Y)
      (CartesianMonoidalCategory.snd X Y))

private theorem prodMap_fst_apply
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    {X Y X' Y' : Sheaf J (Type u)} (f : X ⟶ X') (g : Y ⟶ Y')
    (W : Cᵒᵖ) (x : (X ⨯ Y).obj.obj W) :
    (prod.fst : X' ⨯ Y' ⟶ X').hom.app W ((prod.map f g).hom.app W x) =
      f.hom.app W ((prod.fst : X ⨯ Y ⟶ X).hom.app W x) :=
  congrArg (fun h : X ⨯ Y ⟶ X' ↦ h.hom.app W x) (prod.map_fst f g)

private theorem prodMap_snd_apply
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    {X Y X' Y' : Sheaf J (Type u)} (f : X ⟶ X') (g : Y ⟶ Y')
    (W : Cᵒᵖ) (x : (X ⨯ Y).obj.obj W) :
    (prod.snd : X' ⨯ Y' ⟶ Y').hom.app W ((prod.map f g).hom.app W x) =
      g.hom.app W ((prod.snd : X ⨯ Y ⟶ Y).hom.app W x) :=
  congrArg (fun h : X ⨯ Y ⟶ Y' ↦ h.hom.app W x) (prod.map_snd f g)

private noncomputable abbrev ringSets
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R

private def addSpec
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    {R : Sheaf J CommRingCat.{u}} (M : SheafOfModules.{u} (ringBase R))
    (a : (moduleSets R).obj M ⨯ (moduleSets R).obj M ⟶ (moduleSets R).obj M) : Prop :=
  ∀ W x, a.hom.app W x =
    (show M.val.obj W from (prod.fst : _ ⟶ (moduleSets R).obj M).hom.app W x) +
      (show M.val.obj W from (prod.snd : _ ⟶ (moduleSets R).obj M).hom.app W x)

private def smulSpec
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    {R : Sheaf J CommRingCat.{u}} (M : SheafOfModules.{u} (ringBase R))
    (a : ringSets R ⨯ (moduleSets R).obj M ⟶ (moduleSets R).obj M) : Prop :=
  ∀ W x, a.hom.app W x =
    (show R.obj.obj W from (prod.fst : _ ⟶ ringSets R).hom.app W x) •
      (show M.val.obj W from (prod.snd : _ ⟶ (moduleSets R).obj M).hom.app W x)

private theorem linear_iff
    {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [EssentiallySmall.{u} C]
    {R S : Sheaf J CommRingCat.{u}} (c : R ⟶ S)
    (M : SheafOfModules.{u} (ringBase R)) (N : SheafOfModules.{u} (ringBase S))
    (aM : (moduleSets R).obj M ⨯ (moduleSets R).obj M ⟶ (moduleSets R).obj M)
    (aN : (moduleSets S).obj N ⨯ (moduleSets S).obj N ⟶ (moduleSets S).obj N)
    (sM : ringSets R ⨯ (moduleSets R).obj M ⟶ (moduleSets R).obj M)
    (sN : ringSets S ⨯ (moduleSets S).obj N ⟶ (moduleSets S).obj N)
    (haM : addSpec M aM) (haN : addSpec N aN)
    (hsM : smulSpec M sM) (hsN : smulSpec N sN)
    (α : (moduleSets R).obj M ⟶ (moduleSets S).obj N) :
    (∃ f : M ⟶ (restrictScalars ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).map c)).obj N, (moduleSets R).map f = α) ↔
      aM ≫ α = prod.map α α ≫ aN ∧
      sM ≫ α = prod.map ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u})).map c) α ≫ sN := by
  constructor
  · rintro ⟨f, rfl⟩
    constructor
    · ext W x
      change f.val.app W (aM.hom.app W x) =
        aN.hom.app W ((prod.map ((moduleSets R).map f)
          ((moduleSets R).map f)).hom.app W x)
      rw [haM, haN]
      erw [prodMap_fst_apply, prodMap_snd_apply]
      exact (f.val.app W).hom.map_add _ _
    · ext W x
      change f.val.app W (sM.hom.app W x) =
        sN.hom.app W ((prod.map ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).map c)
          ((moduleSets R).map f)).hom.app W x)
      rw [hsM, hsN]
      erw [prodMap_fst_apply, prodMap_snd_apply]
      exact (f.val.app W).hom.map_smul _ _
  · rintro ⟨ha, hs⟩
    have hAdd W (x y : M.val.obj W) : α.hom.app W (x + y) =
        (show N.val.obj W from α.hom.app W x) +
          (show N.val.obj W from α.hom.app W y) := by
      let p := sectionPair ((moduleSets R).obj M) ((moduleSets R).obj M) W x y
      have h := congrArg (fun f ↦ f.hom.app W p) ha
      change α.hom.app W (aM.hom.app W p) =
        aN.hom.app W ((prod.map α α).hom.app W p) at h
      rw [haM, haN, prodMap_fst_apply, prodMap_snd_apply] at h
      simp only [p, sectionPair_fst, sectionPair_snd] at h
      exact h
    have hSmul W (r : R.obj.obj W) (x : M.val.obj W) : α.hom.app W (r • x) =
        (c.hom.app W r) • (show N.val.obj W from α.hom.app W x) := by
      let p := sectionPair (ringSets R) ((moduleSets R).obj M) W r x
      have h := congrArg (fun f ↦ f.hom.app W p) hs
      change α.hom.app W (sM.hom.app W p) =
        sN.hom.app W ((prod.map ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).map c) α).hom.app W p) at h
      rw [hsM, hsN, prodMap_fst_apply, prodMap_snd_apply] at h
      simp only [p, sectionPair_fst, sectionPair_snd] at h
      exact h
    exact ⟨linearLift α hAdd hSmul, rfl⟩

private theorem product_mate
    {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    [HasBinaryProducts C₀] [HasBinaryProducts D₀]
    {L : C₀ ⥤ D₀} {V : D₀ ⥤ C₀} (adj : L ⊣ V)
    [PreservesFiniteProducts V]
    {X₁ X₂ : C₀} {Y₁ Y₂ : D₀}
    (f₁ : L.obj X₁ ⟶ Y₁) (f₂ : L.obj X₂ ⟶ Y₂) :
    adj.homEquiv (X₁ ⨯ X₂) (Y₁ ⨯ Y₂)
        (prodComparison L X₁ X₂ ≫ prod.map f₁ f₂) =
      prod.map (adj.homEquiv X₁ Y₁ f₁) (adj.homEquiv X₂ Y₂ f₂) ≫
        inv (prodComparison V Y₁ Y₂) := by
  apply (cancel_mono (prodComparison V Y₁ Y₂)).mp
  apply prod.hom_ext
  · simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    simp only [prodComparison_fst, prod.map_fst]
    rw [← adj.homEquiv_naturality_right]
    simp only [Category.assoc, prod.map_fst, prodComparison_fst_assoc]
    exact adj.homEquiv_naturality_left _ _
  · simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    simp only [prodComparison_snd, prod.map_snd]
    rw [← adj.homEquiv_naturality_right]
    simp only [Category.assoc, prod.map_snd, prodComparison_snd_assoc]
    exact adj.homEquiv_naturality_left _ _

private theorem binary_mate_iff
    {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    [HasBinaryProducts C₀] [HasBinaryProducts D₀]
    {L : C₀ ⥤ D₀} {V : D₀ ⥤ C₀} (adj : L ⊣ V)
    [PreservesFiniteProducts V]
    {X₁ X₂ X₃ : C₀} {Y₁ Y₂ Y₃ : D₀}
    (a : X₁ ⨯ X₂ ⟶ X₃) (b : Y₁ ⨯ Y₂ ⟶ Y₃)
    (f₁ : L.obj X₁ ⟶ Y₁) (f₂ : L.obj X₂ ⟶ Y₂)
    (f₃ : L.obj X₃ ⟶ Y₃) :
    L.map a ≫ f₃ = prodComparison L X₁ X₂ ≫ prod.map f₁ f₂ ≫ b ↔
      a ≫ adj.homEquiv X₃ Y₃ f₃ =
        prod.map (adj.homEquiv X₁ Y₁ f₁) (adj.homEquiv X₂ Y₂ f₂) ≫
          inv (prodComparison V Y₁ Y₂) ≫ V.map b := by
  rw [← (adj.homEquiv (X₁ ⨯ X₂) Y₃).injective.eq_iff]
  rw [adj.homEquiv_naturality_left, ← Category.assoc,
    adj.homEquiv_naturality_right, product_mate]
  simp only [Category.assoc]

private theorem binary_mate_iso_iff
    {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    [HasBinaryProducts C₀] [HasBinaryProducts D₀]
    {L : C₀ ⥤ D₀} {V : D₀ ⥤ C₀} (adj : L ⊣ V)
    [PreservesFiniteProducts L] [PreservesFiniteProducts V]
    {X₁ X₂ X₃ P₁ P₂ P₃ : C₀} {I₁ I₂ I₃ Y₁ Y₂ Y₃ : D₀}
    (e₁ : I₁ ≅ L.obj X₁) (e₂ : I₂ ≅ L.obj X₂) (e₃ : I₃ ≅ L.obj X₃)
    (p₁ : P₁ ⟶ V.obj Y₁) (p₂ : P₂ ⟶ V.obj Y₂) (p₃ : P₃ ≅ V.obj Y₃)
    (a : X₁ ⨯ X₂ ⟶ X₃) (aI : I₁ ⨯ I₂ ⟶ I₃)
    (b : Y₁ ⨯ Y₂ ⟶ Y₃) (bP : P₁ ⨯ P₂ ⟶ P₃)
    (hL : L.map a = prodComparison L X₁ X₂ ≫
      prod.map e₁.inv e₂.inv ≫ aI ≫ e₃.hom)
    (hV : bP ≫ p₃.hom = prod.map p₁ p₂ ≫
      inv (prodComparison V Y₁ Y₂) ≫ V.map b)
    (α₁ : I₁ ⟶ Y₁) (α₂ : I₂ ⟶ Y₂) (α₃ : I₃ ⟶ Y₃)
    (β₁ : X₁ ⟶ P₁) (β₂ : X₂ ⟶ P₂) (β₃ : X₃ ⟶ P₃)
    (hm₁ : adj.homEquiv X₁ Y₁ (e₁.inv ≫ α₁) = β₁ ≫ p₁)
    (hm₂ : adj.homEquiv X₂ Y₂ (e₂.inv ≫ α₂) = β₂ ≫ p₂)
    (hm₃ : adj.homEquiv X₃ Y₃ (e₃.inv ≫ α₃) = β₃ ≫ p₃.hom) :
    aI ≫ α₃ = prod.map α₁ α₂ ≫ b ↔
      a ≫ β₃ = prod.map β₁ β₂ ≫ bP := by
  have hl : aI ≫ α₃ = prod.map α₁ α₂ ≫ b ↔
      L.map a ≫ (e₃.inv ≫ α₃) =
        prodComparison L X₁ X₂ ≫
          prod.map (e₁.inv ≫ α₁) (e₂.inv ≫ α₂) ≫ b := by
    rw [hL]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← prod.map_map_assoc]
    simp only [cancel_epi]
  rw [hl, binary_mate_iff adj, hm₁, hm₂, hm₃]
  rw [← prod.map_map_assoc, ← hV]
  simp only [← Category.assoc, cancel_mono]

private theorem right_operation
    {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    [HasBinaryProducts C₀] [HasBinaryProducts D₀]
    (V : D₀ ⥤ C₀) [PreservesFiniteProducts V]
    {P : C₀} {Y : D₀} (e : P ≅ V.obj Y)
    (a : P ⨯ P ⟶ P) (b : Y ⨯ Y ⟶ Y)
    (h : V.map b = prodComparison V Y Y ≫ prod.map e.inv e.inv ≫ a ≫ e.hom) :
    a ≫ e.hom = prod.map e.hom e.hom ≫ inv (prodComparison V Y Y) ≫ V.map b := by
  rw [h]
  simp only [IsIso.inv_hom_id_assoc]
  simp only [prod.map_map_assoc, Iso.hom_inv_id, prod.map_id_id, Category.id_comp]

private theorem right_pair
    {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    [HasBinaryProducts C₀] [HasBinaryProducts D₀]
    (V : D₀ ⥤ C₀) [PreservesFiniteProducts V]
    {P₁ P₂ : C₀} {Y₁ Y₂ : D₀}
    (k : P₁ ⨯ P₂ ⟶ V.obj (Y₁ ⨯ Y₂))
    (p₁ : P₁ ⟶ V.obj Y₁) (p₂ : P₂ ⟶ V.obj Y₂)
    (h₁ : k ≫ V.map prod.fst = prod.fst ≫ p₁)
    (h₂ : k ≫ V.map prod.snd = prod.snd ≫ p₂) :
    k = prod.map p₁ p₂ ≫ inv (prodComparison V Y₁ Y₂) := by
  apply (cancel_mono (prodComparison V Y₁ Y₂)).mp
  apply prod.hom_ext
  · simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    simpa only [prodComparison_fst, prod.map_fst] using h₁
  · simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    simpa only [prodComparison_snd, prod.map_snd] using h₂

private noncomputable def mateIsoEquiv
    {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    {L : C₀ ⥤ D₀} {V : D₀ ⥤ C₀} (adj : L ⊣ V)
    {X P : C₀} {I Y : D₀} (e : I ≅ L.obj X) (p : P ≅ V.obj Y) :
    (I ⟶ Y) ≃ (X ⟶ P) where
  toFun α := adj.homEquiv X Y (e.inv ≫ α) ≫ p.inv
  invFun β := e.hom ≫ (adj.homEquiv X Y).symm (β ≫ p.hom)
  left_inv α := by simp [Category.assoc]
  right_inv β := by simp [Category.assoc]

private theorem mateIsoEquiv_equation
    {C₀ D₀ : Type*} [Category C₀] [Category D₀]
    {L : C₀ ⥤ D₀} {V : D₀ ⥤ C₀} (adj : L ⊣ V)
    {X P : C₀} {I Y : D₀} (e : I ≅ L.obj X) (p : P ≅ V.obj Y)
    (α : I ⟶ Y) :
    adj.homEquiv X Y (e.inv ≫ α) = mateIsoEquiv adj e p α ≫ p.hom := by
  simp [mateIsoEquiv, Category.assoc]

private noncomputable def restrictHomEquiv
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    (F : C₁ ⥤ C₂) (G : C₃ ⥤ C₄) [F.Faithful] [G.Faithful]
    {X₁ X₂ : C₁} {Y₁ Y₂ : C₃}
    (E : (F.obj X₁ ⟶ F.obj X₂) ≃ (G.obj Y₁ ⟶ G.obj Y₂))
    (h : ∀ α, (∃ f : X₁ ⟶ X₂, F.map f = α) ↔
      ∃ g : Y₁ ⟶ Y₂, G.map g = E α) :
    (X₁ ⟶ X₂) ≃ (Y₁ ⟶ Y₂) where
  toFun f := Classical.choose ((h (F.map f)).mp ⟨f, rfl⟩)
  invFun g := Classical.choose ((h (E.symm (G.map g))).mpr
    ⟨g, (E.apply_symm_apply _).symm⟩)
  left_inv f := by
    apply F.map_injective
    have hf := Classical.choose_spec ((h (F.map f)).mp ⟨f, rfl⟩)
    have hg := Classical.choose_spec ((h (E.symm (G.map
      (Classical.choose ((h (F.map f)).mp ⟨f, rfl⟩))))).mpr
        ⟨_, (E.apply_symm_apply _).symm⟩)
    rw [hg, hf, E.symm_apply_apply]
  right_inv g := by
    apply G.map_injective
    have hg := Classical.choose_spec ((h (E.symm (G.map g))).mpr
      ⟨g, (E.apply_symm_apply _).symm⟩)
    have hf := Classical.choose_spec ((h (F.map (Classical.choose
      ((h (E.symm (G.map g))).mpr ⟨g, (E.apply_symm_apply _).symm⟩)))).mp ⟨_, rfl⟩)
    rw [hf, hg, E.apply_symm_apply]

private theorem restrictHomEquiv_map
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    (F : C₁ ⥤ C₂) (G : C₃ ⥤ C₄) [F.Faithful] [G.Faithful]
    {X₁ X₂ : C₁} {Y₁ Y₂ : C₃}
    (E : (F.obj X₁ ⟶ F.obj X₂) ≃ (G.obj Y₁ ⟶ G.obj Y₂))
    (h : ∀ α, (∃ f : X₁ ⟶ X₂, F.map f = α) ↔
      ∃ g : Y₁ ⟶ Y₂, G.map g = E α) (f : X₁ ⟶ X₂) :
    G.map (restrictHomEquiv F G E h f) = E (F.map f) :=
  Classical.choose_spec ((h (F.map f)).mp ⟨f, rfl⟩)

-- Work with abstract functors here to avoid unfolding the sheaf and restriction-of-scalars
-- constructions at every naturality rewrite.
private theorem linear_mate_naturality_left
    {C₀ D₀ M₀ A₀ : Type*} [Category C₀] [Category D₀] [Category M₀] [Category A₀]
    {L : C₀ ⥤ D₀} {V : D₀ ⥤ C₀} (adj : L ⊣ V)
    (F : M₀ ⥤ C₀) (G : A₀ ⥤ D₀) [F.Faithful]
    (I : M₀ ⥤ A₀) (eI : I ⋙ G ≅ F ⋙ L)
    {M N P : M₀} {Y : A₀} (eP : F.obj P ≅ V.obj (G.obj Y))
    (a : M ⟶ N) (f : I.obj N ⟶ Y) (b : M ⟶ P) (b' : N ⟶ P)
    (hb : F.map b ≫ eP.hom = adj.homEquiv _ _ (eI.inv.app M ≫ G.map (I.map a ≫ f)))
    (hb' : F.map b' ≫ eP.hom = adj.homEquiv _ _ (eI.inv.app N ≫ G.map f)) :
    b = a ≫ b' := by
  apply F.map_injective
  apply (cancel_mono eP.hom).mp
  rw [hb, F.map_comp, Category.assoc, hb', G.map_comp]
  have hn : eI.inv.app M ≫ G.map (I.map a) = L.map (F.map a) ≫ eI.inv.app N :=
    (eI.inv.naturality a).symm
  rw [← Category.assoc, hn, Category.assoc, adj.homEquiv_naturality_left]

private theorem linear_mate_naturality_right
    {C₀ D₀ M₀ A₀ : Type*} [Category C₀] [Category D₀] [Category M₀] [Category A₀]
    {L : C₀ ⥤ D₀} {V : D₀ ⥤ C₀} (adj : L ⊣ V)
    (F : M₀ ⥤ C₀) (G : A₀ ⥤ D₀) [F.Faithful]
    {M P P' : M₀} {I Y Y' : A₀} (eI : G.obj I ≅ L.obj (F.obj M))
    (eP : F.obj P ≅ V.obj (G.obj Y)) (eP' : F.obj P' ≅ V.obj (G.obj Y'))
    (f : I ⟶ Y) (q : Y ⟶ Y') (p : P ⟶ P') (g : M ⟶ P) (g' : M ⟶ P')
    (hg : F.map g ≫ eP.hom = adj.homEquiv _ _ (eI.inv ≫ G.map f))
    (hg' : F.map g' ≫ eP'.hom = adj.homEquiv _ _ (eI.inv ≫ G.map (f ≫ q)))
    (hp : F.map p ≫ eP'.hom = eP.hom ≫ V.map (G.map q)) :
    g' = g ≫ p := by
  apply F.map_injective
  apply (cancel_mono eP'.hom).mp
  rw [hg', F.map_comp, Category.assoc, hp, ← Category.assoc, hg, G.map_comp,
    ← Category.assoc, adj.homEquiv_naturality_right]

private theorem linear_mate_iff
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteProducts L] [PreservesFiniteProducts V]
    {R : Sheaf J CommRingCat.{u}} {S A : Sheaf K CommRingCat.{u}}
    (eR : ringSets A ≅ L.obj (ringSets R)) (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringBase R)) (MI : SheafOfModules.{u} (ringBase A))
    (H : SheafOfModules.{u} (ringBase S)) (PH : SheafOfModules.{u} (ringBase R))
    (eM : (moduleSets A).obj MI ≅ L.obj ((moduleSets R).obj M))
    (eH : (moduleSets R).obj PH ≅ V.obj ((moduleSets S).obj H))
    (hI : ∃ (aM : (moduleSets R).obj M ⨯ (moduleSets R).obj M ⟶ (moduleSets R).obj M)
      (sM : ringSets R ⨯ (moduleSets R).obj M ⟶ (moduleSets R).obj M)
      (aI : (moduleSets A).obj MI ⨯ (moduleSets A).obj MI ⟶ (moduleSets A).obj MI)
      (sI : ringSets A ⨯ (moduleSets A).obj MI ⟶ (moduleSets A).obj MI),
      addSpec M aM ∧ smulSpec M sM ∧ addSpec MI aI ∧ smulSpec MI sI ∧
      L.map aM = prodComparison L _ _ ≫ prod.map eM.inv eM.inv ≫ aI ≫ eM.hom ∧
      L.map sM = prodComparison L _ _ ≫ prod.map eR.inv eM.inv ≫ sI ≫ eM.hom)
    (hP : ∃ (aH : (moduleSets S).obj H ⨯ (moduleSets S).obj H ⟶ (moduleSets S).obj H)
      (sH : ringSets S ⨯ (moduleSets S).obj H ⟶ (moduleSets S).obj H)
      (aP : (moduleSets R).obj PH ⨯ (moduleSets R).obj PH ⟶ (moduleSets R).obj PH)
      (sP : ringSets R ⨯ (moduleSets R).obj PH ⟶ (moduleSets R).obj PH)
      (k : ringSets R ⨯ (moduleSets R).obj PH ⟶
        V.obj (ringSets S ⨯ (moduleSets S).obj H)),
      addSpec H aH ∧ smulSpec H sH ∧ addSpec PH aP ∧ smulSpec PH sP ∧
      V.map aH = prodComparison V _ _ ≫ prod.map eH.inv eH.inv ≫ aP ≫ eH.hom ∧
      k ≫ V.map prod.fst = prod.fst ≫ adj.homEquiv _ _
        (eR.inv ≫ (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).map c) ∧
      k ≫ V.map prod.snd = prod.snd ≫ eH.hom ∧ sP ≫ eH.hom = k ≫ V.map sH)
    (α : (moduleSets A).obj MI ⟶ (moduleSets S).obj H) :
    (∃ f : MI ⟶ (restrictScalars ((sheafCompose K
      (forget₂ CommRingCat.{u} RingCat.{u})).map c)).obj H, (moduleSets A).map f = α) ↔
      ∃ g : M ⟶ PH, (moduleSets R).map g = mateIsoEquiv adj eM eH α := by
  have : K.HasSheafCompose (CategoryTheory.forget CommRingCat.{u}) := inferInstance
  obtain ⟨aM, sM, aI, sI, haM, hsM, haI, hsI, hLA, hLS⟩ := hI
  obtain ⟨aH, sH, aP, sP, k, haH, hsH, haP, hsP, hVA, hk₁, hk₂, hks⟩ := hP
  have hRightAdd := right_operation V eH aP aH hVA
  have hk := right_pair V k
    (adj.homEquiv _ _ (eR.inv ≫ (sheafCompose K
      (CategoryTheory.forget CommRingCat)).map c)) eH.hom hk₁ hk₂
  have hRightSmul : sP ≫ eH.hom =
      prod.map (adj.homEquiv _ _ (eR.inv ≫ (sheafCompose K
        (CategoryTheory.forget CommRingCat)).map c)) eH.hom ≫
          inv (prodComparison V (ringSets S) ((moduleSets S).obj H)) ≫ V.map sH := by
    rw [hks, hk]
    simp only [Category.assoc]
  let β := mateIsoEquiv adj eM eH α
  have hm : adj.homEquiv _ _ (eM.inv ≫ α) = β ≫ eH.hom :=
    mateIsoEquiv_equation adj eM eH α
  have hAdd := binary_mate_iso_iff adj eM eM eM
    eH.hom eH.hom eH aM aI aH aP
    hLA hRightAdd α α α (β) (β) (β) hm hm hm
  have hSmul := binary_mate_iso_iff adj eR eM eM
    (adj.homEquiv _ _ (eR.inv ≫ (sheafCompose K
      (CategoryTheory.forget CommRingCat)).map c))
    eH.hom eH sM sI sH sP hLS hRightSmul
    ((sheafCompose K (CategoryTheory.forget CommRingCat)).map c) α α
    (𝟙 (ringSets R)) (β) (β)
    (by exact (Category.id_comp _).symm) hm hm
  have hSame := linear_iff (𝟙 R) M PH aM aP sM sP
    haM haP hsM hsP (β)
  exact (linear_iff c MI H aI aH sI sH haI haH hsI hsH α).trans
    ((and_congr hAdd hSmul).trans hSame.symm)

private theorem linear_mate_equiv
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
    [PreservesFiniteProducts L] [PreservesFiniteProducts V]
    {R : Sheaf J CommRingCat.{u}} {S A : Sheaf K CommRingCat.{u}}
    (eR : ringSets A ≅ L.obj (ringSets R)) (c : A ⟶ S)
    (I : SheafOfModules.{u} (ringBase R) ⥤ SheafOfModules.{u} (ringBase A))
    (P : SheafOfModules.{u} (ringBase S) ⥤ SheafOfModules.{u} (ringBase R))
    (eI : I ⋙ moduleSets A ≅ moduleSets R ⋙ L)
    (eP : P ⋙ moduleSets R ≅ moduleSets S ⋙ V)
    (hI : ∀ M, ∃ (aM : (moduleSets R).obj M ⨯ (moduleSets R).obj M ⟶ (moduleSets R).obj M)
      (sM : ringSets R ⨯ (moduleSets R).obj M ⟶ (moduleSets R).obj M)
      (aI : (moduleSets A).obj (I.obj M) ⨯ (moduleSets A).obj (I.obj M) ⟶
        (moduleSets A).obj (I.obj M))
      (sI : ringSets A ⨯ (moduleSets A).obj (I.obj M) ⟶ (moduleSets A).obj (I.obj M)),
      addSpec M aM ∧ smulSpec M sM ∧ addSpec (I.obj M) aI ∧ smulSpec (I.obj M) sI ∧
      L.map aM = prodComparison L _ _ ≫
        prod.map (eI.inv.app M) (eI.inv.app M) ≫ aI ≫ eI.hom.app M ∧
      L.map sM = prodComparison L _ _ ≫ prod.map eR.inv (eI.inv.app M) ≫ sI ≫ eI.hom.app M)
    (hP : ∀ H, ∃ (aH : (moduleSets S).obj H ⨯ (moduleSets S).obj H ⟶ (moduleSets S).obj H)
      (sH : ringSets S ⨯ (moduleSets S).obj H ⟶ (moduleSets S).obj H)
      (aP : (moduleSets R).obj (P.obj H) ⨯ (moduleSets R).obj (P.obj H) ⟶
        (moduleSets R).obj (P.obj H))
      (sP : ringSets R ⨯ (moduleSets R).obj (P.obj H) ⟶ (moduleSets R).obj (P.obj H))
      (k : ringSets R ⨯ (moduleSets R).obj (P.obj H) ⟶
        V.obj (ringSets S ⨯ (moduleSets S).obj H)),
      addSpec H aH ∧ smulSpec H sH ∧ addSpec (P.obj H) aP ∧ smulSpec (P.obj H) sP ∧
      V.map aH = prodComparison V _ _ ≫
        prod.map (eP.inv.app H) (eP.inv.app H) ≫ aP ≫ eP.hom.app H ∧
      k ≫ V.map prod.fst = prod.fst ≫ adj.homEquiv _ _
        (eR.inv ≫ (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).map c) ∧
      k ≫ V.map prod.snd = prod.snd ≫ eP.hom.app H ∧ sP ≫ eP.hom.app H = k ≫ V.map sH)
    : ∃ B : ∀ M H, (I.obj M ⟶ (restrictScalars
        ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)).obj H) ≃ (M ⟶ P.obj H),
      (∀ {M N} (a : M ⟶ N) H f, B M H (I.map a ≫ f) = a ≫ B N H f) ∧
      (∀ M {H H'} f (b : H ⟶ H'), B M H' (f ≫ (restrictScalars
        ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)).map b) = B M H f ≫ P.map b) ∧
      ∀ M H f, (moduleSets R).map (B M H f) ≫ eP.hom.app H =
        adj.homEquiv _ _ (eI.inv.app M ≫ (moduleSets A).map f) := by
  have : K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := inferInstance
  let Q := restrictScalars ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map c)
  let E : ∀ M H, ((moduleSets A).obj (I.obj M) ⟶ (moduleSets S).obj H) ≃
      ((moduleSets R).obj M ⟶ (moduleSets R).obj (P.obj H)) :=
    fun M H ↦ mateIsoEquiv adj (eI.app M) (eP.app H)
  have hImage M H (α : (moduleSets A).obj (I.obj M) ⟶ (moduleSets S).obj H) :
      (∃ f : I.obj M ⟶ (restrictScalars ((sheafCompose K
        (forget₂ CommRingCat RingCat)).map c)).obj H, (moduleSets A).map f = α) ↔
        ∃ g : M ⟶ P.obj H, (moduleSets R).map g = E M H α := by
    exact linear_mate_iff L V adj eR c M (I.obj M) H (P.obj H)
      (eI.app M) (eP.app H) (hI M) (hP H) α
  let B : ∀ M H, (I.obj M ⟶ (restrictScalars ((sheafCompose K
      (forget₂ CommRingCat RingCat)).map c)).obj H) ≃ (M ⟶ P.obj H) :=
    fun M H ↦ restrictHomEquiv (moduleSets A) (moduleSets R) (E M H) (hImage M H)
  have hB M H f : (moduleSets R).map (B M H f) ≫ eP.hom.app H =
      adj.homEquiv _ _ (eI.inv.app M ≫ (moduleSets A).map f) := by
    rw [restrictHomEquiv_map]
    exact (mateIsoEquiv_equation adj (eI.app M) (eP.app H) _).symm
  refine ⟨B, ?_, ?_, hB⟩
  · intro M N a H f
    exact linear_mate_naturality_left adj (moduleSets R) (moduleSets A) I eI
      (Y := Q.obj H) (eP.app H) a f _ _ (hB M H _) (hB N H f)
  · intro M H H' f b
    exact linear_mate_naturality_right adj (moduleSets R) (moduleSets A)
      (Y := Q.obj H) (Y' := Q.obj H') (eI.app M) (eP.app H) (eP.app H') f (Q.map b)
      (P.map b) _ _ (hB M H f) (hB M H' _) (eP.hom.naturality b)

end Helpers

-- The statement records every operation and its underlying comparison.

/-- Transport module structures and restrict the given set adjunction to linear maps.
Source: Stacks Project, Tags 03D1--03D3, `lemma-pushforward-module`,
`lemma-pullback-module`, `lemma-adjoint-push-pull-modules`, and Tag 03D7,
`lemma-adjoint-pullback-pushforward-modules`.
(auxiliary; not a blueprint node).

Proof: L preserves finite products by hypothesis, and V does so because it is a
right adjoint. Transport the addition, zero, inverse and scalar-action diagrams
of M through L and its product comparisons; the ring compatibility hRing supplies
the coefficient identification. Evaluating these diagrams gives I(M) and their
naturality gives I on maps and eI. Transport H through V in the same way and
restrict scalars along the adjunct of c to get P(H), its maps, and eP. The inverse
product comparison for V applied to the pair consisting of the adjunct of c and
the underlying comparison for H gives k. Its projections and scalar formula are
the comparison equations. For an A-linear alpha from I(M) to H restricted along c,
transpose eI.inv followed by its underlying map under adj and use eP to identify
the codomain. Naturality of the adjunction unit on the source addition and scalar
actions, and its product projections, shows that this transpose is R-linear.
Conversely the same equations, using injectivity of adj.homEquiv, imply that the
inverse transpose of an R-linear map is A-linear. The two inverse identities are
those of adj.homEquiv. The induced bijection B is natural because eI, eP, and the
original adjunction are natural; forgetting linearity gives the last equation.
This argument uses no tensor product or scalar-extension adjunction. -/
theorem geometric_module_transport
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    :
    letI : ∀ X Y : Sheaf J (Type u), HasBinaryProduct X Y := fun _ _ ↦ inferInstance
    letI : ∀ X Y : Sheaf K (Type u), HasBinaryProduct X Y := fun _ _ ↦ inferInstance
    ∀ (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ V) [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (A : Sheaf K CommRingCat.{u}) (eR : ((sheafCompose K (CategoryTheory.forget
      CommRingCat.{u})).obj A) ≅ L.obj ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
      R))
      (addR mulR : (Limits.prod ((sheafCompose J
        (CategoryTheory.forget CommRingCat.{u})).obj R)
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)) ⟶
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R))
      (addA mulA : (Limits.prod ((sheafCompose K
        (CategoryTheory.forget CommRingCat.{u})).obj A)
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)) ⟶
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A))
    (_hRing : (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).obj.obj W),
        addR.hom.app W x = @Add.add (R.obj.obj W) inferInstance (((prod.fst : ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R)).hom.app W x) : R.obj.obj W) (((prod.snd : ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) :
          R.obj.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).obj.obj W),
        mulR.hom.app W x = @Mul.mul (R.obj.obj W) inferInstance (((prod.fst : ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R)).hom.app W x) : R.obj.obj W) (((prod.snd : ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) :
          R.obj.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).obj.obj W),
        addA.hom.app W x = @Add.add (A.obj.obj W) inferInstance (((prod.fst : ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A)).hom.app W x) : A.obj.obj W) (((prod.snd : ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).hom.app W x) :
          A.obj.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).obj.obj W),
        mulA.hom.app W x = @Mul.mul (A.obj.obj W) inferInstance (((prod.fst : ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A)).hom.app W x) : A.obj.obj W) (((prod.snd : ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).hom.app W x) :
          A.obj.obj W)) ∧
      L.map addR = prodComparison L ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ≫
        prod.map eR.inv eR.inv ≫ addA ≫ eR.hom ∧
      L.map mulR = prodComparison L ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ≫
        prod.map eR.inv eR.inv ≫ mulA ≫ eR.hom)
    (c : A ⟶ S),
      ∃ (I : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
        SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A))
        (P : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
          SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
        (eI : I ⋙ (toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
          sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})) ≅ (toSheaf ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})) ⋙ L)
        (eP : P ⋙ (toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})) ≅ (toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})) ⋙ V),
        (∀ M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
          ∃ (addM : ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
            sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
            (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J (forget₂
            CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
            AddCommGrpCat.{u})).obj M))
            (muM : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj M))
            (addI : ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
              sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K
              (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (I.obj M)))
            (muI : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((toSheaf
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K
              (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (I.obj M))),
      (∀ (W : Cᵒᵖ) (x : (((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf ((sheafCompose
        J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
        AddCommGrpCat.{u})).obj M)).obj.obj W),
        addM.hom.app W x = @Add.add (M.val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
          M)).hom.app W x) : M.val.obj W) (((prod.snd : ((toSheaf ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶
          ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M)).hom.app W x) : M.val.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
        (CategoryTheory.forget AddCommGrpCat.{u})).obj M)).obj.obj W),
        muM.hom.app W x = @SMul.smul (R.obj.obj W) (M.val.obj W) inferInstance (((prod.fst :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) : R.obj.obj W) (((prod.snd :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj M)).hom.app W x) : M.val.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M))).obj.obj W),
        addI.hom.app W x = @Add.add ((I.obj M).val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (I.obj M))).hom.app W x) : (I.obj M).val.obj W) (((prod.snd : ((toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (I.obj M)) ⟶ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
          sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M))).hom.app W x) :
          (I.obj M).val.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯
        ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M))).obj.obj W),
        muI.hom.app W x = @SMul.smul (A.obj.obj W) ((I.obj M).val.obj W) inferInstance (((prod.fst :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj A)).hom.app W x) : A.obj.obj W) (((prod.snd :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (I.obj M))).hom.app W x) : (I.obj M).val.obj W)) ∧
          L.map addM = prodComparison L ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
            RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M)
            ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose
            J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
            prod.map (eI.inv.app M) (eI.inv.app M) ≫ addI ≫ eI.hom.app M ∧
          L.map muM = prodComparison L ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
            R) ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
            sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
            prod.map eR.inv (eI.inv.app M) ≫ muI ≫ eI.hom.app M) ∧
        (∀ H : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S),
          ∃ (addH : ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
            sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf
            ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
            (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K (forget₂
            CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
            AddCommGrpCat.{u})).obj H))
            (muH : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
              (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K
              (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj H))
            (addP : ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
              sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (P.obj H)))
            (muP : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (P.obj H)))
            (k : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ V.obj (((sheafCompose K
              (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf ((sheafCompose K (forget₂
              CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj H))),
      (∀ (W : Dᵒᵖ) (x : (((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf ((sheafCompose
        K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
        AddCommGrpCat.{u})).obj H)).obj.obj W),
        addH.hom.app W x = @Add.add (H.val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf ((sheafCompose K (forget₂
          CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
          H)).hom.app W x) : H.val.obj W) (((prod.snd : ((toSheaf ((sheafCompose K (forget₂
          CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶
          ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H)).hom.app W x) : H.val.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯
        ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{u})).obj H)).obj.obj W),
        muH.hom.app W x = @SMul.smul (S.obj.obj W) (H.val.obj W) inferInstance (((prod.fst :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj S)).hom.app W x) : S.obj.obj W) (((prod.snd :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K (forget₂
          CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj H)).hom.app W x) : H.val.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H))).obj.obj W),
        addP.hom.app W x = @Add.add ((P.obj H).val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (P.obj H))).hom.app W x) : (P.obj H).val.obj W) (((prod.snd : ((toSheaf ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (P.obj H)) ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H))).hom.app W x) :
          (P.obj H).val.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H))).obj.obj W),
        muP.hom.app W x = @SMul.smul (R.obj.obj W) ((P.obj H).val.obj W) inferInstance (((prod.fst :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) : R.obj.obj W) (((prod.snd :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (P.obj H))).hom.app W x) : (P.obj H).val.obj W)) ∧
          V.map addH = prodComparison V ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
            RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H)
            ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose
            K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ≫
            prod.map (eP.inv.app H) (eP.inv.app H) ≫ addP ≫ eP.hom.app H ∧
          k ≫ V.map (prod.fst : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯
            ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose
            K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((sheafCompose K
            (CategoryTheory.forget CommRingCat.{u})).obj S)) =
            (prod.fst : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((sheafCompose J
              (CategoryTheory.forget CommRingCat.{u})).obj R)) ≫
              adj.homEquiv ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)
                ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S)
                (eR.inv ≫ (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).map c) ∧
          k ≫ V.map (prod.snd : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯
            ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose
            K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K
            (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
            AddCommGrpCat.{u})).obj H)) =
            (prod.snd : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (P.obj H))) ≫ eP.hom.app H ∧
          muP ≫ eP.hom.app H = k ≫ V.map muH) ∧
        ∃ B : ∀ (M : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
            (H : SheafOfModules.{u}
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S)),
            (I.obj M ⟶ (restrictScalars
              ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)).obj H) ≃ (M ⟶ P.obj H),
          (∀ {M N} (a : M ⟶ N) H f, B M H (I.map a ≫ f) = a ≫ B N H f) ∧
          (∀ M {H H'} f (b : H ⟶ H'),
            B M H' (f ≫ (restrictScalars
              ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)).map b) =
              B M H f ≫ P.map b) ∧
          ∀ M H f,
            (toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⋙
              sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).map (B M H f) ≫
                eP.hom.app H =
              adj.homEquiv _ _ (eI.inv.app M ≫
                (toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj A) ⋙
                  sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).map f)
 := by
  dsimp only
  intro L V adj hL R S A eR addR mulR addA mulA hRing c
  let : ∀ X Y : Sheaf J (Type u), HasBinaryProduct X Y := sheafHasBinaryProduct
  let : ∀ X Y : Sheaf K (Type u), HasBinaryProduct X Y := sheafHasBinaryProduct
  let : PreservesLimits V := adj.rightAdjoint_preservesLimits
  obtain ⟨I, P, eI, eP, hI, hP⟩ :=
    geometric_module_construction J K L V adj R S A eR addR mulR addA mulA hRing c
  refine ⟨I, P, eI, eP, hI, hP, ?_⟩
  exact linear_mate_equiv L V adj eR c I P eI eP hI hP

end SheafOfModules
