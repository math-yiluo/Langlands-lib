/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalExtRepresentative

/-! # Generic assembly of a transported Ext class

Source: diagonal tower coefficient changes (1), and limit (3).
(blueprint: lem-diagonal-cyclic-ext-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u₁ v₁ u₂ v₂ w₁ w₂ t₁ t₂ u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 5000] cyclicSmallShiftedSingleHom

attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.homEquiv
  Ext.comp Ext.mk₀ Ext.mapExactFunctor Functor.mapDerivedCategory shiftFunctor

private theorem transportArrow
    {C₀ C₁ D₀ D₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    (G : C₀ ⥤ D₁) (R : C₀ ⥤ C₁) (F : C₁ ⥤ D₁) (E : D₀ ⥤ D₁)
    {P Q : C₀} {K J S T : D₀} {X Z U : D₁}
    (δ : P ⟶ Q) (f : K ⟶ J) (e : G ≅ R ⋙ F)
    (sa : F.obj (R.obj P) ≅ E.obj K) (ta : F.obj (R.obj Q) ≅ E.obj J)
    (a : K ≅ S) (b : J ≅ T) (j : E.obj S ≅ U)
    (σ : X ⟶ G.obj P) (τ : G.obj Q ⟶ Z) (u : X ⟶ U) (v : E.obj T ⟶ Z)
    (hs : σ ≫ e.hom.app P ≫ sa.hom ≫ E.map a.hom ≫ j.hom = u)
    (ht : E.map b.inv ≫ ta.inv ≫ e.inv.app Q ≫ τ = v)
    (hf : F.map (R.map δ) = sa.hom ≫ E.map f ≫ ta.inv) :
    σ ≫ G.map δ ≫ τ = u ≫ j.inv ≫ E.map (a.inv ≫ f ≫ b.hom) ≫ v := by
  have hS : σ ≫ e.hom.app P ≫ sa.hom = u ≫ j.inv ≫ E.map a.inv := by
    have h := hs =≫ j.inv ≫ E.map a.inv
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, ← E.map_comp,
      a.hom_inv_id, E.map_id, Category.comp_id] using h
  have hT : ta.inv ≫ e.inv.app Q ≫ τ = E.map b.hom ≫ v := by
    have h := E.map b.hom ≫= ht
    simpa only [Category.assoc, ← E.map_comp_assoc, b.hom_inv_id,
      E.map_id, Category.id_comp] using h
  have hn : G.map δ = e.hom.app P ≫ F.map (R.map δ) ≫ e.inv.app Q := by
    change G.map δ = e.hom.app P ≫ (R ⋙ F).map δ ≫ e.inv.app Q
    rw [← e.hom.naturality_assoc]
    simp only [Iso.hom_inv_id_app, Category.comp_id]
  rw [hn, hf]
  simp only [Category.assoc]
  rw [reassoc_of% hS]
  rw [hT]
  simp only [Functor.map_comp, Category.assoc]

private theorem finiteExtRepresentative
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} B]
    [HasExt.{w₁} C] [HasExt.{w₂} B]
    (F : C ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} {P Q : B} {n : ℕ}
    (s : F.obj X ≅ P) (t : F.obj Y ≅ Q) (c : Ext.{w₁} X Y n) :
    ((Ext.mk₀ s.inv).comp
      ((c.mapExactFunctor F : Ext.{w₂} (F.obj X) (F.obj Y) n).comp
        (Ext.mk₀ t.hom) (add_zero n)) (zero_add n)).hom =
      (DerivedCategory.singleFunctor B 0).map s.inv ≫
        (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
        F.mapDerivedCategory.map c.hom ≫
        (F.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor B 0).map t.hom)⟦(n : ℤ)⟧' := by
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    ShiftedHom.comp_mk₀, Ext.mapExactFunctor_hom, ShiftedHom.map, Category.assoc]

/-- The endpoint squares and finite arrow equation transport the Ext class.
Source: diagonal finite-reduction comparisons, formal arrow and Ext assembly.
(blueprint: lem-diagonal-cyclic-ext-assembly).
Proof: use naturality of e to replace G(delta), then the finite arrow equation.
The source square cancels the source isomorphisms. The target square cancels the
root isomorphisms. The representative equation for c and exact-functor Ext-to-Hom
formula identify the result with the normalized evaluation. Ext.homEquiv is injective. -/
theorem cyclicExtAssembly
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{t₁} C] [HasDerivedCategory.{t₂} B]
    [HasExt.{w₁} C] [HasExt.{w₂} B]
    {C₀ C₁ : Type*} [Category C₀] [Category C₁]
    (G : C₀ ⥤ DerivedCategory B) (R : C₀ ⥤ C₁) (F : C₁ ⥤ DerivedCategory B)
    (E : C ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    {X Y : C} {P Q : B} {n : ℕ} {P₀ Q₀ : C₀} {K J : DerivedCategory C}
    (δ : P₀ ⟶ Q₀) (f : K ⟶ J) (e : G ≅ R ⋙ F)
    (sa : F.obj (R.obj P₀) ≅ E.mapDerivedCategory.obj K)
    (ta : F.obj (R.obj Q₀) ≅ E.mapDerivedCategory.obj J)
    (a : K ≅ (DerivedCategory.singleFunctor C 0).obj X)
    (b : J ≅ ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧)
    (s : E.obj X ≅ P) (t : E.obj Y ≅ Q)
    (σ : (DerivedCategory.singleFunctor B 0).obj P ⟶ G.obj P₀)
    (τ : G.obj Q₀ ⟶ ((DerivedCategory.singleFunctor B 0).obj Q)⟦(n : ℤ)⟧)
    (c : Ext.{w₁} X Y n) (d : Ext.{w₂} P Q n)
    (hc : c.hom = a.inv ≫ f ≫ b.hom)
    (hrep : cyclicExtRepresentative d = σ ≫ G.map δ ≫ τ)
    (hs : σ ≫ e.hom.app P₀ ≫ sa.hom ≫ E.mapDerivedCategory.map a.hom ≫
        (E.mapDerivedCategorySingleFunctor 0).hom.app X =
      (DerivedCategory.singleFunctor B 0).map s.inv)
    (ht : E.mapDerivedCategory.map b.inv ≫ ta.inv ≫ e.inv.app Q₀ ≫ τ =
      (E.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
        ((E.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor B 0).map t.hom)⟦(n : ℤ)⟧')
    (hf : F.map (R.map δ) = sa.hom ≫ E.mapDerivedCategory.map f ≫ ta.inv) :
    d = (Ext.mk₀ s.inv).comp
      ((c.mapExactFunctor E : Ext.{w₂} (E.obj X) (E.obj Y) n).comp
        (Ext.mk₀ t.hom) (add_zero n)) (zero_add n) := by
  unfold cyclicExtRepresentative at hrep
  apply Ext.homEquiv.injective
  change d.hom = _
  rw [hrep]
  calc
    _ = (DerivedCategory.singleFunctor B 0).map s.inv ≫
        (E.mapDerivedCategorySingleFunctor 0).inv.app X ≫
        E.mapDerivedCategory.map c.hom ≫
        (E.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
        ((E.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor B 0).map t.hom)⟦(n : ℤ)⟧' := by
      rw [hc]
      exact transportArrow G R F E.mapDerivedCategory δ f e sa ta a b
        ((E.mapDerivedCategorySingleFunctor 0).app X) σ τ
        ((DerivedCategory.singleFunctor B 0).map s.inv)
        ((E.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
          ((E.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' ≫
          ((DerivedCategory.singleFunctor B 0).map t.hom)⟦(n : ℤ)⟧') hs ht hf
    _ = _ := (finiteExtRepresentative E s t c).symm

/-- Combine the coefficient comparison, arrow equation and finite-cycle equality.
Source: diagonal limit (3) (blueprint: lem-diagonal-cyclic-ext-assembly).
Proof: eliminate the supplied coefficient comparison. Apply cyclicExtAssembly
using its two squares, then compose with the given finite-cycle equality. -/
theorem cyclicExtAssembly_of_comparison
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [dC : HasDerivedCategory.{t₁} C] [dB : HasDerivedCategory.{t₂} B]
    [eC : HasExt.{v₁} C] [eB : HasExt.{v₂} B]
    {C₀ : Type u₃} [Category.{v₃} C₀]
    {C₁ : Type u₄} [Category.{v₄} C₁]
    (G : C₀ ⥤ DerivedCategory B) (R : C₀ ⥤ C₁) (F : C₁ ⥤ DerivedCategory B)
    (E : C ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    {P₀ Q₀ : C₀} {X Y : C} {P Q : B} {K J : DerivedCategory C}
    (n : ℕ) (δ : P₀ ⟶ Q₀) (f : K ⟶ J)
    (a : K ≅ (DerivedCategory.singleFunctor C 0).obj X)
    (b : J ≅ ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧)
    (s : E.obj X ≅ P) (t : E.obj Y ≅ Q)
    (σ : (DerivedCategory.singleFunctor B 0).obj P ⟶ G.obj P₀)
    (τ : G.obj Q₀ ⟶ ((DerivedCategory.singleFunctor B 0).obj Q)⟦(n : ℤ)⟧)
    (sa : F.obj (R.obj P₀) ≅ E.mapDerivedCategory.obj K)
    (ta : F.obj (R.obj Q₀) ≅ E.mapDerivedCategory.obj J)
    (comparison : ∃ e : G ≅ R ⋙ F,
      (σ ≫ e.hom.app P₀ ≫ sa.hom ≫ E.mapDerivedCategory.map a.hom ≫
      (E.mapDerivedCategorySingleFunctor 0).hom.app X =
    (DerivedCategory.singleFunctor B 0).map s.inv) ∧
      (E.mapDerivedCategory.map b.inv ≫ ta.inv ≫ e.inv.app Q₀ ≫ τ =
    (E.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
      ((E.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor B 0).map t.hom)⟦(n : ℤ)⟧'))
    (hf : F.map (R.map δ) = sa.hom ≫ E.mapDerivedCategory.map f ≫ ta.inv)
    (c : Ext.{v₁} X Y n) (hc : c.hom = a.inv ≫ f ≫ b.hom)
    (d : Ext.{v₂} P Q n)
    (hrep : cyclicExtRepresentative d = σ ≫ G.map δ ≫ τ)
    (goalClass : Ext.{v₂} P Q n)
    (hcycle : (Ext.mk₀ s.inv).comp
      ((c.mapExactFunctor E : Ext.{v₂} (E.obj X) (E.obj Y) n).comp
        (Ext.mk₀ t.hom) (add_zero n)) (zero_add n) = goalClass) :
    d = goalClass := by
  obtain ⟨e, hs, ht⟩ := comparison
  exact (cyclicExtAssembly G R F E δ f e sa ta a b s t σ τ c d hc hrep hs ht hf).trans
    hcycle

/-- Assemble normalized finite witnesses before specializing their categories.
Source: diagonal limit (3) (blueprint: lem-diagonal-cyclic-ext-assembly).
Proof: eliminate the two finite endpoints and two arrow endpoints in the abstract
categories. Their normalizations give the coefficient comparison; the previous
assembly theorem combines that comparison, the arrow and the cycle equation. -/
theorem cyclicExtAssembly_of_normalizations
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [dC : HasDerivedCategory.{t₁} C] [dB : HasDerivedCategory.{t₂} B]
    [eC : HasExt.{v₁} C] [eB : HasExt.{v₂} B]
    {C₀ : Type u₃} [Category.{v₃} C₀]
    {C₁ : Type u₄} [Category.{v₄} C₁]
    (G : C₀ ⥤ DerivedCategory B) (R : C₀ ⥤ C₁) (F : C₁ ⥤ DerivedCategory B)
    (E : C ⥤ B) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    {P₀ Q₀ : C₀} {X Y : C} {P Q : B} {K J : DerivedCategory C}
    (n : ℕ) (δ : P₀ ⟶ Q₀) (f : K ⟶ J)
    (a : K ≅ (DerivedCategory.singleFunctor C 0).obj X)
    (b : J ≅ ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧)
    (σ : (DerivedCategory.singleFunctor B 0).obj P ⟶ G.obj P₀)
    (τ : G.obj Q₀ ⟶ ((DerivedCategory.singleFunctor B 0).obj Q)⟦(n : ℤ)⟧)
    (sourceNorm : (E.obj X ≅ P) → Prop) (targetNorm : (E.obj Y ≅ Q) → Prop)
    (sourceArrowNorm : (F.obj (R.obj P₀) ≅ E.mapDerivedCategory.obj K) → Prop)
    (targetArrowNorm : (F.obj (R.obj Q₀) ≅ E.mapDerivedCategory.obj J) → Prop)
    (c : Ext.{v₁} X Y n) (hc : c.hom = a.inv ≫ f ≫ b.hom)
    (d : Ext.{v₂} P Q n)
    (hrep : cyclicExtRepresentative d = σ ≫ G.map δ ≫ τ)
    (goalClass : Ext.{v₂} P Q n)
    (finite : ∃ (s : E.obj X ≅ P) (t : E.obj Y ≅ Q),
      sourceNorm s ∧ targetNorm t ∧
        (Ext.mk₀ s.inv).comp
          ((c.mapExactFunctor E : Ext.{v₂} (E.obj X) (E.obj Y) n).comp
            (Ext.mk₀ t.hom) (add_zero n)) (zero_add n) = goalClass)
    (arrows : ∃ (sa : F.obj (R.obj P₀) ≅ E.mapDerivedCategory.obj K)
        (ta : F.obj (R.obj Q₀) ≅ E.mapDerivedCategory.obj J),
      sourceArrowNorm sa ∧ targetArrowNorm ta ∧
        F.map (R.map δ) = sa.hom ≫ E.mapDerivedCategory.map f ≫ ta.inv)
    (comparison : ∀ (s : E.obj X ≅ P) (t : E.obj Y ≅ Q),
      sourceNorm s → targetNorm t →
      ∀ (sa : F.obj (R.obj P₀) ≅ E.mapDerivedCategory.obj K)
        (ta : F.obj (R.obj Q₀) ≅ E.mapDerivedCategory.obj J),
      sourceArrowNorm sa → targetArrowNorm ta →
      ∃ e : G ≅ R ⋙ F,
        (σ ≫ e.hom.app P₀ ≫ sa.hom ≫ E.mapDerivedCategory.map a.hom ≫
          (E.mapDerivedCategorySingleFunctor 0).hom.app X =
          (DerivedCategory.singleFunctor B 0).map s.inv) ∧
        (E.mapDerivedCategory.map b.inv ≫ ta.inv ≫ e.inv.app Q₀ ≫ τ =
          (E.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
            ((E.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧' ≫
            ((DerivedCategory.singleFunctor B 0).map t.hom)⟦(n : ℤ)⟧')) :
    d = goalClass := by
  obtain ⟨s, t, hs, ht, hcycle⟩ := finite
  obtain ⟨sa, ta, hsa, hta, hf⟩ := arrows
  exact cyclicExtAssembly_of_comparison G R F E n δ f a b s t σ τ sa ta
    (comparison s t hs ht sa ta hsa hta) hf c hc d hrep goalClass hcycle

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
