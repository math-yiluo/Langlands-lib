/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicExtEvaluationAssembly

/-! # The normalized assembly contract with fixed representative endpoints

Source: diagonal limit (3).
(blueprint: def-diagonal-cyclic-pointwise-assembly).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe uA vA tA tS u₃ v₃ u₄ v₄
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 5000] cyclicSmallShiftedSingleHom

attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.homEquiv
  Ext.comp Ext.mk₀ Ext.mapExactFunctor Functor.mapDerivedCategory shiftFunctor

/-- Literal normalized assembly after the representative functor and endpoints are fixed.
Source: coefficient changes (1) (blueprint: def-diagonal-cyclic-pointwise-assembly).
All arrows, classes, normalizations and comparison squares remain parameters. -/
@[irreducible] def cyclicPointwiseAssemblySpec
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [dA : HasDerivedCategory.{tA} A]
    [dS : HasDerivedCategory.{tS} (ℕᵒᵖ ⥤ A)]
    [eA : HasExt.{vA} A] [eS : HasExt.{vA} (ℕᵒᵖ ⥤ A)]
    {C₀ : Type u₃} [Category.{v₃} C₀] (k : ℕ)
    {P₀ Q₀ : C₀} {P Q : A}
    (G : C₀ ⥤ DerivedCategory A)
    (σ : (DerivedCategory.singleFunctor A 0).obj P ⟶ G.obj P₀)
    (τ : G.obj Q₀ ⟶ ((DerivedCategory.singleFunctor A 0).obj Q)⟦(2 : ℤ)⟧) : Prop :=
  let En : (ℕᵒᵖ ⥤ A) ⥤ A := (evaluation ℕᵒᵖ A).obj (op k)
  ∀ (R : C₀ ⥤ C₀) (F : C₀ ⥤ DerivedCategory A)
    {X Y : (ℕᵒᵖ ⥤ A)} {K J : DerivedCategory (ℕᵒᵖ ⥤ A)}
    (δ : P₀ ⟶ Q₀) (f : K ⟶ J)
    (a : K ≅ (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj X)
    (b : J ≅ ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj Y)⟦(2 : ℤ)⟧)
    (sourceNorm : (En.obj X ≅ P) → Prop) (targetNorm : (En.obj Y ≅ Q) → Prop)
    (sourceArrowNorm : (F.obj (R.obj P₀) ≅ En.mapDerivedCategory.obj K) → Prop)
    (targetArrowNorm : (F.obj (R.obj Q₀) ≅ En.mapDerivedCategory.obj J) → Prop)
    (c : Ext.{vA} X Y 2) (_hc : c.hom = a.inv ≫ f ≫ b.hom)
    (d : Ext.{vA} P Q 2)
    (_hrep : cyclicExtRepresentative d = σ ≫ G.map δ ≫ τ)
    (goalClass : Ext.{vA} P Q 2)
    (_finite : ∃ (s : En.obj X ≅ P) (t : En.obj Y ≅ Q),
      sourceNorm s ∧ targetNorm t ∧
        (Ext.mk₀ s.inv).comp
          ((c.mapExactFunctor En : Ext.{vA} (En.obj X) (En.obj Y) 2).comp
            (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2) = goalClass)
    (_arrows : ∃ (sa : F.obj (R.obj P₀) ≅ En.mapDerivedCategory.obj K)
        (ta : F.obj (R.obj Q₀) ≅ En.mapDerivedCategory.obj J),
      sourceArrowNorm sa ∧ targetArrowNorm ta ∧
        F.map (R.map δ) = sa.hom ≫ En.mapDerivedCategory.map f ≫ ta.inv)
    (_comparison : ∀ (s : En.obj X ≅ P) (t : En.obj Y ≅ Q),
      sourceNorm s → targetNorm t →
      ∀ (sa : F.obj (R.obj P₀) ≅ En.mapDerivedCategory.obj K)
        (ta : F.obj (R.obj Q₀) ≅ En.mapDerivedCategory.obj J),
      sourceArrowNorm sa → targetArrowNorm ta →
      ∃ e : G ≅ R ⋙ F,
        (σ ≫ e.hom.app P₀ ≫ sa.hom ≫ En.mapDerivedCategory.map a.hom ≫
          (En.mapDerivedCategorySingleFunctor 0).hom.app X =
          (DerivedCategory.singleFunctor A 0).map s.inv) ∧
        (En.mapDerivedCategory.map b.inv ≫ ta.inv ≫ e.inv.app Q₀ ≫ τ =
          (En.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
            ((En.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(2 : ℤ)⟧' ≫
            ((DerivedCategory.singleFunctor A 0).map t.hom)⟦(2 : ℤ)⟧')),
    d = goalClass

attribute [local semireducible] cyclicEvaluationAssemblySpec

/-- A universal normalized evaluation contract gives its fixed-endpoint instance.
Source: coefficient changes (1) (blueprint: def-diagonal-cyclic-pointwise-assembly).
Proof: unfold the literal contract and specialize the universal statement to its
fixed functor, endpoints and degree two. -/
theorem cyclicPointwiseAssembly_of_spec
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [dA : HasDerivedCategory.{tA} A]
    [dS : HasDerivedCategory.{tS} (ℕᵒᵖ ⥤ A)]
    [eA : HasExt.{vA} A] [eS : HasExt.{vA} (ℕᵒᵖ ⥤ A)]
    {C₀ : Type u₃} [Category.{v₃} C₀] (k : ℕ)
    {P₀ Q₀ : C₀} {P Q : A}
    (G : C₀ ⥤ DerivedCategory A)
    (σ : (DerivedCategory.singleFunctor A 0).obj P ⟶ G.obj P₀)
    (τ : G.obj Q₀ ⟶ ((DerivedCategory.singleFunctor A 0).obj Q)⟦(2 : ℤ)⟧)
    (h : cyclicEvaluationAssemblySpec (A := A) (C₀ := C₀) k) :
    cyclicPointwiseAssemblySpec k G σ τ := by
  unfold cyclicPointwiseAssemblySpec
  dsimp only
  intro R F X Y K J δ f a b sourceNorm targetNorm sourceArrowNorm targetArrowNorm
    c hc d hrep goalClass finite arrows comparison
  exact h G R F 2 δ f a b σ τ sourceNorm targetNorm sourceArrowNorm targetArrowNorm
    c hc d hrep goalClass finite arrows comparison

/-- The same assembly contract after fixing the reduction functors, arrow and norms.
Source: coefficient changes (1) (blueprint: def-diagonal-cyclic-pointwise-assembly).
The completed arrow and both Ext classes still vary. -/
@[irreducible] def cyclicArrowAssemblySpec
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [dA : HasDerivedCategory.{tA} A]
    [dS : HasDerivedCategory.{tS} (ℕᵒᵖ ⥤ A)]
    [eA : HasExt.{vA} A] [eS : HasExt.{vA} (ℕᵒᵖ ⥤ A)]
    {C₀ : Type u₃} [Category.{v₃} C₀] (k : ℕ)
    {P₀ Q₀ : C₀} {P Q : A}
    (G : C₀ ⥤ DerivedCategory A)
    (σ : (DerivedCategory.singleFunctor A 0).obj P ⟶ G.obj P₀)
    (τ : G.obj Q₀ ⟶ ((DerivedCategory.singleFunctor A 0).obj Q)⟦(2 : ℤ)⟧)
    (R : C₀ ⥤ C₀) (F : C₀ ⥤ DerivedCategory A)
    {X Y : (ℕᵒᵖ ⥤ A)} {K J : DerivedCategory (ℕᵒᵖ ⥤ A)}
    (f : K ⟶ J)
    (a : K ≅ (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj X)
    (b : J ≅ ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj Y)⟦(2 : ℤ)⟧)
    (sourceNorm : (((evaluation ℕᵒᵖ A).obj (op k)).obj X ≅ P) → Prop)
    (targetNorm : (((evaluation ℕᵒᵖ A).obj (op k)).obj Y ≅ Q) → Prop)
    (sourceArrowNorm : (F.obj (R.obj P₀) ≅
      ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.obj K) → Prop)
    (targetArrowNorm : (F.obj (R.obj Q₀) ≅
      ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.obj J) → Prop) : Prop :=
  let En : (ℕᵒᵖ ⥤ A) ⥤ A := (evaluation ℕᵒᵖ A).obj (op k)
  ∀ (δ : P₀ ⟶ Q₀)
    (c : Ext.{vA} X Y 2) (_hc : c.hom = a.inv ≫ f ≫ b.hom)
    (d : Ext.{vA} P Q 2)
    (_hrep : cyclicExtRepresentative d = σ ≫ G.map δ ≫ τ)
    (goalClass : Ext.{vA} P Q 2)
    (_finite : ∃ (s : En.obj X ≅ P) (t : En.obj Y ≅ Q),
      sourceNorm s ∧ targetNorm t ∧
        (Ext.mk₀ s.inv).comp
          ((c.mapExactFunctor En : Ext.{vA} (En.obj X) (En.obj Y) 2).comp
            (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2) = goalClass)
    (_arrows : ∃ (sa : F.obj (R.obj P₀) ≅ En.mapDerivedCategory.obj K)
        (ta : F.obj (R.obj Q₀) ≅ En.mapDerivedCategory.obj J),
      sourceArrowNorm sa ∧ targetArrowNorm ta ∧
        F.map (R.map δ) = sa.hom ≫ En.mapDerivedCategory.map f ≫ ta.inv)
    (_comparison : ∀ (s : En.obj X ≅ P) (t : En.obj Y ≅ Q),
      sourceNorm s → targetNorm t →
      ∀ (sa : F.obj (R.obj P₀) ≅ En.mapDerivedCategory.obj K)
        (ta : F.obj (R.obj Q₀) ≅ En.mapDerivedCategory.obj J),
      sourceArrowNorm sa → targetArrowNorm ta →
      ∃ e : G ≅ R ⋙ F,
        (σ ≫ e.hom.app P₀ ≫ sa.hom ≫ En.mapDerivedCategory.map a.hom ≫
          (En.mapDerivedCategorySingleFunctor 0).hom.app X =
          (DerivedCategory.singleFunctor A 0).map s.inv) ∧
        (En.mapDerivedCategory.map b.inv ≫ ta.inv ≫ e.inv.app Q₀ ≫ τ =
          (En.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
            ((En.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(2 : ℤ)⟧' ≫
            ((DerivedCategory.singleFunctor A 0).map t.hom)⟦(2 : ℤ)⟧')),
    d = goalClass

attribute [local semireducible] cyclicPointwiseAssemblySpec

/-- Fixed reduction data, with all four normalization predicates still varying.
Source: diagonal limit (3) (blueprint: def-diagonal-cyclic-pointwise-assembly).
This delays the actual cone equations until the final application. -/
@[irreducible] def cyclicFixedArrowAssemblySpec
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [dA : HasDerivedCategory.{tA} A]
    [dS : HasDerivedCategory.{tS} (ℕᵒᵖ ⥤ A)]
    [eA : HasExt.{vA} A] [eS : HasExt.{vA} (ℕᵒᵖ ⥤ A)]
    {C₀ : Type u₃} [Category.{v₃} C₀] (k : ℕ)
    {P₀ Q₀ : C₀} {P Q : A}
    (G : C₀ ⥤ DerivedCategory A)
    (σ : (DerivedCategory.singleFunctor A 0).obj P ⟶ G.obj P₀)
    (τ : G.obj Q₀ ⟶ ((DerivedCategory.singleFunctor A 0).obj Q)⟦(2 : ℤ)⟧)
    (R : C₀ ⥤ C₀) (F : C₀ ⥤ DerivedCategory A)
    {X Y : (ℕᵒᵖ ⥤ A)} {K J : DerivedCategory (ℕᵒᵖ ⥤ A)}
    (f : K ⟶ J)
    (a : K ≅ (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj X)
    (b : J ≅ ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj Y)⟦(2 : ℤ)⟧)
    : Prop :=
  ∀ (sourceNorm : (((evaluation ℕᵒᵖ A).obj (op k)).obj X ≅ P) → Prop)
    (targetNorm : (((evaluation ℕᵒᵖ A).obj (op k)).obj Y ≅ Q) → Prop)
    (sourceArrowNorm : (F.obj (R.obj P₀) ≅
      ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.obj K) → Prop)
    (targetArrowNorm : (F.obj (R.obj Q₀) ≅
      ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.obj J) → Prop),
    cyclicArrowAssemblySpec k G σ τ R F f a b
      sourceNorm targetNorm sourceArrowNorm targetArrowNorm

/-- Assembly after the source and root comparisons have already been supplied.
Source: diagonal limit (3) (blueprint: def-diagonal-cyclic-pointwise-assembly).
Only the representative, finite cycle and finite arrow equations remain inputs. -/
@[irreducible] def cyclicResolvedAssemblySpec
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [dA : HasDerivedCategory.{tA} A]
    [dS : HasDerivedCategory.{tS} (ℕᵒᵖ ⥤ A)]
    [eA : HasExt.{vA} A] [eS : HasExt.{vA} (ℕᵒᵖ ⥤ A)]
    {C₀ : Type u₃} [Category.{v₃} C₀] (k : ℕ)
    {P₀ Q₀ : C₀} {P Q : A}
    (G : C₀ ⥤ DerivedCategory A)
    (σ : (DerivedCategory.singleFunctor A 0).obj P ⟶ G.obj P₀)
    (τ : G.obj Q₀ ⟶ ((DerivedCategory.singleFunctor A 0).obj Q)⟦(2 : ℤ)⟧)
    (R : C₀ ⥤ C₀) (F : C₀ ⥤ DerivedCategory A)
    {X Y : (ℕᵒᵖ ⥤ A)} {K J : DerivedCategory (ℕᵒᵖ ⥤ A)}
    (f : K ⟶ J)
    (a : K ≅ (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj X)
    (b : J ≅ ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj Y)⟦(2 : ℤ)⟧)
    (sourceNorm : (((evaluation ℕᵒᵖ A).obj (op k)).obj X ≅ P) → Prop)
    (targetNorm : (((evaluation ℕᵒᵖ A).obj (op k)).obj Y ≅ Q) → Prop)
    (sourceArrowNorm : (F.obj (R.obj P₀) ≅
      ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.obj K) → Prop)
    (targetArrowNorm : (F.obj (R.obj Q₀) ≅
      ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.obj J) → Prop) : Prop :=
  let En : (ℕᵒᵖ ⥤ A) ⥤ A := (evaluation ℕᵒᵖ A).obj (op k)
  ∀ (δ : P₀ ⟶ Q₀)
    (c : Ext.{vA} X Y 2) (_hc : c.hom = a.inv ≫ f ≫ b.hom)
    (d : Ext.{vA} P Q 2)
    (_hrep : cyclicExtRepresentative d = σ ≫ G.map δ ≫ τ)
    (goalClass : Ext.{vA} P Q 2)
    (_finite : ∃ (s : En.obj X ≅ P) (t : En.obj Y ≅ Q),
      sourceNorm s ∧ targetNorm t ∧
        (Ext.mk₀ s.inv).comp
          ((c.mapExactFunctor En : Ext.{vA} (En.obj X) (En.obj Y) 2).comp
            (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2) = goalClass)
    (_arrows : ∃ (sa : F.obj (R.obj P₀) ≅ En.mapDerivedCategory.obj K)
        (ta : F.obj (R.obj Q₀) ≅ En.mapDerivedCategory.obj J),
      sourceArrowNorm sa ∧ targetArrowNorm ta ∧
        F.map (R.map δ) = sa.hom ≫ En.mapDerivedCategory.map f ≫ ta.inv),
    d = goalClass

attribute [local semireducible] cyclicArrowAssemblySpec

/-- Fix endpoint comparison before introducing classes and their representatives.
Source: diagonal limit (3) (blueprint: def-diagonal-cyclic-pointwise-assembly).
Proof: introduce the remaining class and arrow arguments, then apply assembly
with the fixed endpoint comparison. -/
theorem cyclicResolvedAssembly_of_comparison
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [dA : HasDerivedCategory.{tA} A]
    [dS : HasDerivedCategory.{tS} (ℕᵒᵖ ⥤ A)]
    [eA : HasExt.{vA} A] [eS : HasExt.{vA} (ℕᵒᵖ ⥤ A)]
    {C₀ : Type u₃} [Category.{v₃} C₀] (k : ℕ)
    {P₀ Q₀ : C₀} {P Q : A}
    (G : C₀ ⥤ DerivedCategory A)
    (σ : (DerivedCategory.singleFunctor A 0).obj P ⟶ G.obj P₀)
    (τ : G.obj Q₀ ⟶ ((DerivedCategory.singleFunctor A 0).obj Q)⟦(2 : ℤ)⟧)
    (R : C₀ ⥤ C₀) (F : C₀ ⥤ DerivedCategory A)
    {X Y : (ℕᵒᵖ ⥤ A)} {K J : DerivedCategory (ℕᵒᵖ ⥤ A)}
    (f : K ⟶ J)
    (a : K ≅ (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj X)
    (b : J ≅ ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj Y)⟦(2 : ℤ)⟧)
    (sourceNorm : (((evaluation ℕᵒᵖ A).obj (op k)).obj X ≅ P) → Prop)
    (targetNorm : (((evaluation ℕᵒᵖ A).obj (op k)).obj Y ≅ Q) → Prop)
    (sourceArrowNorm : (F.obj (R.obj P₀) ≅
      ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.obj K) → Prop)
    (targetArrowNorm : (F.obj (R.obj Q₀) ≅
      ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.obj J) → Prop)
    (h : cyclicArrowAssemblySpec k G σ τ R F f a b
      sourceNorm targetNorm sourceArrowNorm targetArrowNorm)
    (comparison : ∀ (s : ((evaluation ℕᵒᵖ A).obj (op k)).obj X ≅ P)
      (t : ((evaluation ℕᵒᵖ A).obj (op k)).obj Y ≅ Q),
      sourceNorm s → targetNorm t →
      ∀ (sa : F.obj (R.obj P₀) ≅ ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.obj K)
        (ta : F.obj (R.obj Q₀) ≅ ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.obj J),
      sourceArrowNorm sa → targetArrowNorm ta →
      ∃ e : G ≅ R ⋙ F,
        (σ ≫ e.hom.app P₀ ≫ sa.hom ≫ ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.map a.hom ≫
          (((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategorySingleFunctor 0).hom.app X =
          (DerivedCategory.singleFunctor A 0).map s.inv) ∧
        (((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.map b.inv ≫ ta.inv ≫ e.inv.app Q₀ ≫ τ =
          (((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
            ((((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategorySingleFunctor 0).hom.app
              Y)⟦(2 : ℤ)⟧' ≫
            ((DerivedCategory.singleFunctor A 0).map t.hom)⟦(2 : ℤ)⟧')) :
    cyclicResolvedAssemblySpec k G σ τ R F f a b
      sourceNorm targetNorm sourceArrowNorm targetArrowNorm := by
  unfold cyclicResolvedAssemblySpec
  dsimp only
  intro δ c hc d hrep goalClass finite arrows
  exact h δ c hc d hrep goalClass finite arrows comparison

/-- Fix the quotient and strict arrow before introducing normalization predicates.
Source: diagonal limit (3) (blueprint: def-diagonal-cyclic-pointwise-assembly).
Proof: introduce the four predicates and varying arrow, then specialize the
universal pointwise contract. All class arguments are left unapplied. -/
theorem cyclicFixedArrowAssembly_of_pointwise
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [dA : HasDerivedCategory.{tA} A]
    [dS : HasDerivedCategory.{tS} (ℕᵒᵖ ⥤ A)]
    [eA : HasExt.{vA} A] [eS : HasExt.{vA} (ℕᵒᵖ ⥤ A)]
    {C₀ : Type u₃} [Category.{v₃} C₀] (k : ℕ)
    {P₀ Q₀ : C₀} {P Q : A}
    (G : C₀ ⥤ DerivedCategory A)
    (σ : (DerivedCategory.singleFunctor A 0).obj P ⟶ G.obj P₀)
    (τ : G.obj Q₀ ⟶ ((DerivedCategory.singleFunctor A 0).obj Q)⟦(2 : ℤ)⟧)
    (R : C₀ ⥤ C₀) (F : C₀ ⥤ DerivedCategory A)
    {X Y : (ℕᵒᵖ ⥤ A)} {K J : DerivedCategory (ℕᵒᵖ ⥤ A)}
    (f : K ⟶ J)
    (a : K ≅ (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj X)
    (b : J ≅ ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj Y)⟦(2 : ℤ)⟧)
    (h : cyclicPointwiseAssemblySpec k G σ τ) :
    cyclicFixedArrowAssemblySpec k G σ τ R F f a b := by
  unfold cyclicFixedArrowAssemblySpec
  intro sourceNorm targetNorm sourceArrowNorm targetArrowNorm
  unfold cyclicArrowAssemblySpec
  dsimp only
  intro δ
  exact h R F δ f a b sourceNorm targetNorm sourceArrowNorm targetArrowNorm

/-- A realized class with a specified representative equals the fixed solution.
Source: diagonal limit (3) (blueprint: def-diagonal-cyclic-pointwise-assembly).
This literal predicate contains no strict class or family data. -/
@[irreducible] def cyclicRepresentativeSolution
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [dA : HasDerivedCategory.{tA} A] [eA : HasExt.{vA} A]
    {C₀ : Type u₃} [Category.{v₃} C₀] {P₀ Q₀ : C₀} {P Q : A}
    (G : C₀ ⥤ DerivedCategory A)
    (σ : (DerivedCategory.singleFunctor A 0).obj P ⟶ G.obj P₀)
    (τ : G.obj Q₀ ⟶ ((DerivedCategory.singleFunctor A 0).obj Q)⟦(2 : ℤ)⟧)
    (δ : P₀ ⟶ Q₀) (goalClass : Ext.{vA} P Q 2) : Prop :=
  ∀ (d : Ext.{vA} P Q 2),
    cyclicExtRepresentative d = σ ≫ G.map δ ≫ τ → d = goalClass

attribute [local semireducible] cyclicResolvedAssemblySpec

/-- Insert the strict class, finite cycle and finite arrow before the realized class.
Source: diagonal limit (3) (blueprint: def-diagonal-cyclic-pointwise-assembly).
Proof: introduce an arbitrary realized class with its representative and apply
resolved assembly with the fixed strict class and finite equations. -/
theorem cyclicRepresentativeSolution_of_resolved
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [dA : HasDerivedCategory.{tA} A]
    [dS : HasDerivedCategory.{tS} (ℕᵒᵖ ⥤ A)]
    [eA : HasExt.{vA} A] [eS : HasExt.{vA} (ℕᵒᵖ ⥤ A)]
    {C₀ : Type u₃} [Category.{v₃} C₀] (k : ℕ)
    {P₀ Q₀ : C₀} {P Q : A}
    (G : C₀ ⥤ DerivedCategory A)
    (σ : (DerivedCategory.singleFunctor A 0).obj P ⟶ G.obj P₀)
    (τ : G.obj Q₀ ⟶ ((DerivedCategory.singleFunctor A 0).obj Q)⟦(2 : ℤ)⟧)
    (R : C₀ ⥤ C₀) (F : C₀ ⥤ DerivedCategory A)
    {X Y : (ℕᵒᵖ ⥤ A)} {K J : DerivedCategory (ℕᵒᵖ ⥤ A)}
    (f : K ⟶ J)
    (a : K ≅ (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj X)
    (b : J ≅ ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj Y)⟦(2 : ℤ)⟧)
    (sourceNorm : (((evaluation ℕᵒᵖ A).obj (op k)).obj X ≅ P) → Prop)
    (targetNorm : (((evaluation ℕᵒᵖ A).obj (op k)).obj Y ≅ Q) → Prop)
    (sourceArrowNorm : (F.obj (R.obj P₀) ≅
      ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.obj K) → Prop)
    (targetArrowNorm : (F.obj (R.obj Q₀) ≅
      ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.obj J) → Prop)
    (h : cyclicResolvedAssemblySpec
      (dA := dA) (dS := dS) (eA := eA) (eS := eS) k G σ τ R F f a b
      sourceNorm targetNorm sourceArrowNorm targetArrowNorm)
    (δ : P₀ ⟶ Q₀)
    (c : Ext.{vA} X Y 2) (hc : c.hom = a.inv ≫ f ≫ b.hom)
    (goalClass : Ext.{vA} P Q 2)
    (finite : ∃ (s : ((evaluation ℕᵒᵖ A).obj (op k)).obj X ≅ P)
      (t : ((evaluation ℕᵒᵖ A).obj (op k)).obj Y ≅ Q),
      sourceNorm s ∧ targetNorm t ∧
        (Ext.mk₀ s.inv).comp
          ((c.mapExactFunctor ((evaluation ℕᵒᵖ A).obj (op k)) :
            Ext.{vA} (((evaluation ℕᵒᵖ A).obj (op k)).obj X)
              (((evaluation ℕᵒᵖ A).obj (op k)).obj Y) 2).comp
            (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2) = goalClass)
    (arrows : ∃ (sa : F.obj (R.obj P₀) ≅ ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.obj K)
        (ta : F.obj (R.obj Q₀) ≅ ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.obj J),
      sourceArrowNorm sa ∧ targetArrowNorm ta ∧
        F.map (R.map δ) = sa.hom ≫
          ((evaluation ℕᵒᵖ A).obj (op k)).mapDerivedCategory.map f ≫ ta.inv)
    : cyclicRepresentativeSolution (dA := dA) (eA := eA) G σ τ δ goalClass := by
  unfold cyclicRepresentativeSolution
  intro d hrep
  exact h δ c hc d hrep goalClass finite arrows

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
