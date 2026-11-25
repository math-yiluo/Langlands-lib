/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalExtRepresentative
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicExtAssembly

/-! # Ext assembly at one evaluation of strict diagonal systems

Source: diagonal limit (3).
(blueprint: lem-diagonal-cyclic-ext-evaluation-assembly).
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

/-- The normalized evaluation assembly contract with abstract coefficient categories.
Source: diagonal limit (3) (blueprint: lem-diagonal-cyclic-ext-evaluation-assembly).
This is the literal finite cycle, arrow and endpoint argument, not a chosen object. -/
@[irreducible] def cyclicEvaluationAssemblySpec
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [dA : HasDerivedCategory.{tA} A]
    [dS : HasDerivedCategory.{tS} (ℕᵒᵖ ⥤ A)]
    [eA : HasExt.{vA} A] [eS : HasExt.{vA} (ℕᵒᵖ ⥤ A)]
    {C₀ : Type u₃} [Category.{v₃} C₀] (k : ℕ) : Prop :=
  let En : (ℕᵒᵖ ⥤ A) ⥤ A := (evaluation ℕᵒᵖ A).obj (op k)
  ∀ (G : C₀ ⥤ DerivedCategory A) (R : C₀ ⥤ C₀) (F : C₀ ⥤ DerivedCategory A)
    {P₀ Q₀ : C₀} {X Y : (ℕᵒᵖ ⥤ A)} {P Q : A} {K J : DerivedCategory
      (ℕᵒᵖ ⥤ A)}
    (m : ℕ) (δ : P₀ ⟶ Q₀) (f : K ⟶ J)
    (a : K ≅ (DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj X)
    (b : J ≅ ((DerivedCategory.singleFunctor (ℕᵒᵖ ⥤ A) 0).obj Y)⟦(m : ℤ)⟧)
    (σ : (DerivedCategory.singleFunctor A 0).obj P ⟶ G.obj P₀)
    (τ : G.obj Q₀ ⟶ ((DerivedCategory.singleFunctor A 0).obj Q)⟦(m : ℤ)⟧)
    (sourceNorm : (En.obj X ≅ P) → Prop) (targetNorm : (En.obj Y ≅ Q) → Prop)
    (sourceArrowNorm : (F.obj (R.obj P₀) ≅ En.mapDerivedCategory.obj K) → Prop)
    (targetArrowNorm : (F.obj (R.obj Q₀) ≅ En.mapDerivedCategory.obj J) → Prop)
    (c : Ext.{vA} X Y m) (_hc : c.hom = a.inv ≫ f ≫ b.hom)
    (d : Ext.{vA} P Q m)
    (_hrep : cyclicExtRepresentative d = σ ≫ G.map δ ≫ τ)
    (goalClass : Ext.{vA} P Q m)
    (_finite : ∃ (s : En.obj X ≅ P) (t : En.obj Y ≅ Q),
      sourceNorm s ∧ targetNorm t ∧
        (Ext.mk₀ s.inv).comp
          ((c.mapExactFunctor En : Ext.{vA} (En.obj X) (En.obj Y) m).comp
            (Ext.mk₀ t.hom) (add_zero m)) (zero_add m) = goalClass)
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
          (En.mapDerivedCategory.commShiftIso (m : ℤ)).hom.app _ ≫
            ((En.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(m : ℤ)⟧' ≫
            ((DerivedCategory.singleFunctor A 0).map t.hom)⟦(m : ℤ)⟧')),
    d = goalClass

/-- Normalized evaluation assembly before substituting geometric objects or classes.
Source: diagonal limit (3) (blueprint: lem-diagonal-cyclic-ext-evaluation-assembly).
Proof: unfold the literal contract and use normalized generic Ext assembly for exact
level evaluation. All coefficient categories, endpoints and classes remain parameters. -/
theorem cyclicExtAssembly_atLevel
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [dA : HasDerivedCategory.{tA} A]
    [dS : HasDerivedCategory.{tS} (ℕᵒᵖ ⥤ A)]
    [eA : HasExt.{vA} A] [eS : HasExt.{vA} (ℕᵒᵖ ⥤ A)]
    {C₀ : Type u₃} [Category.{v₃} C₀] (k : ℕ) :
    cyclicEvaluationAssemblySpec (A := A) (C₀ := C₀) k := by
  unfold cyclicEvaluationAssemblySpec
  dsimp only
  intro G R F P₀ Q₀ X Y P Q K J m δ f a b σ τ
    sourceNorm targetNorm sourceArrowNorm targetArrowNorm c hc d hrep goalClass
    finite arrows comparison
  exact cyclicExtAssembly_of_normalizations
    (C := ℕᵒᵖ ⥤ A) (B := A) (dC := dS) (dB := dA) (eC := eS) (eB := eA)
    G R F ((evaluation ℕᵒᵖ A).obj (op k)) m δ f a b σ τ
    sourceNorm targetNorm sourceArrowNorm targetArrowNorm c hc d hrep goalClass
    finite arrows comparison

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
