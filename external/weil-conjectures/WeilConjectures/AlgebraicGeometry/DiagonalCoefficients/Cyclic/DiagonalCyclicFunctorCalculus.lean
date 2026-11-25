/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassReduction
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalExtRepresentative

/-! # Generic finite evaluation and completed-reference functor calculations

Source: diagonal tower coefficient changes (1), and limit (3).
(blueprint: def-diagonal-cyclic-functor-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u u₁ v₁ u₂ v₂ w₁ w₂ t₁ t₂
universe a₀ a₁ a₂ a₃ a₄ b₀ b₁ b₂ b₃ b₄ d₀ d₁ d₂ d₃ d₄
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients


attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  Functor.mapDerivedCategory shiftFunctor

/-- An explicit functorial composite used by cyclic transport.
Source: coefficient changes (1), exact-single and shift comparisons.
(blueprint: def-diagonal-cyclic-functor-calculus). -/
@[irreducible] def threeFunctorSource
    {A₁ : Type a₁} [Category.{b₁} A₁] [Abelian A₁]
    {A₂ : Type a₂} [Category.{b₂} A₂] [Abelian A₂]
    {A₃ : Type a₃} [Category.{b₃} A₃] [Abelian A₃]
    {A₄ : Type a₄} [Category.{b₄} A₄] [Abelian A₄]
    [HasDerivedCategory.{d₁} A₁] [HasDerivedCategory.{d₂} A₂]
    [HasDerivedCategory.{d₃} A₃] [HasDerivedCategory.{d₄} A₄]
    (R : DerivedCategory A₁ ⥤ DerivedCategory A₂)
    (G : A₂ ⥤ A₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A₃ ⥤ A₄) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {X₁ : A₁} {X₂ : A₂} {X₃ : A₃}
    (q : (DerivedCategory.singleFunctor A₂ 0).obj X₂ ⟶
      R.obj ((DerivedCategory.singleFunctor A₁ 0).obj X₁))
    (s : G.obj X₂ ≅ X₃) :
    (DerivedCategory.singleFunctor A₄ 0).obj (H.obj X₃) ⟶
      (R ⋙ G.mapDerivedCategory ⋙ H.mapDerivedCategory).obj
        ((DerivedCategory.singleFunctor A₁ 0).obj X₁) :=
  (H.mapDerivedCategorySingleFunctor 0).inv.app X₃ ≫
    H.mapDerivedCategory.map
      ((DerivedCategory.singleFunctor A₃ 0).map s.inv ≫
        (G.mapDerivedCategorySingleFunctor 0).inv.app X₂ ≫ G.mapDerivedCategory.map q)

/-- An explicit functorial composite used by cyclic transport.
Source: coefficient changes (1), exact-single and shift comparisons.
(blueprint: def-diagonal-cyclic-functor-calculus). -/
@[irreducible] def threeFunctorTarget
    {A₁ : Type a₁} [Category.{b₁} A₁] [Abelian A₁]
    {A₂ : Type a₂} [Category.{b₂} A₂] [Abelian A₂]
    {A₃ : Type a₃} [Category.{b₃} A₃] [Abelian A₃]
    {A₄ : Type a₄} [Category.{b₄} A₄] [Abelian A₄]
    [HasDerivedCategory.{d₁} A₁] [HasDerivedCategory.{d₂} A₂]
    [HasDerivedCategory.{d₃} A₃] [HasDerivedCategory.{d₄} A₄]
    (R : DerivedCategory A₁ ⥤ DerivedCategory A₂)
    (G : A₂ ⥤ A₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A₃ ⥤ A₄) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (n : ℕ) {Y₁ : A₁} {Y₂ : A₂} {Y₃ : A₃}
    (r : R.obj (((DerivedCategory.singleFunctor A₁ 0).obj Y₁)⟦(n : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor A₂ 0).obj Y₂)⟦(n : ℤ)⟧)
    (t : G.obj Y₂ ≅ Y₃) :
    (R ⋙ G.mapDerivedCategory ⋙ H.mapDerivedCategory).obj
        (((DerivedCategory.singleFunctor A₁ 0).obj Y₁)⟦(n : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor A₄ 0).obj (H.obj Y₃))⟦(n : ℤ)⟧ :=
  H.mapDerivedCategory.map
      (G.mapDerivedCategory.map r ≫
        (G.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
        ((G.mapDerivedCategorySingleFunctor 0).hom.app Y₂)⟦(n : ℤ)⟧' ≫
        ((DerivedCategory.singleFunctor A₃ 0).map t.hom)⟦(n : ℤ)⟧') ≫
    (H.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
    ((H.mapDerivedCategorySingleFunctor 0).hom.app Y₃)⟦(n : ℤ)⟧'

/-- Exact functors carry the actual Ext representative to the single-arrow map.
Source: Mathlib Ext.mapExactFunctor_hom.
(blueprint: def-diagonal-cyclic-functor-calculus).
Proof: unfold the representative and single-arrow map, then apply the Ext formula. -/
theorem mapExactFunctorRepresentative
    {A : Type a₃} [Category.{b₃} A] [Abelian A]
    {B : Type a₄} [Category.{b₄} B] [Abelian B]
    [HasDerivedCategory.{d₃} A] [HasDerivedCategory.{d₄} B]
    [HasExt.{w₁} A] [HasExt.{w₂} B]
    (H : A ⥤ B) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {X Y : A} {n : ℕ} (c : Ext.{w₁} X Y n) :
    cyclicExtRepresentative (c.mapExactFunctor H : Ext.{w₂} (H.obj X) (H.obj Y) n) =
      SpTowerClasses.mapSingleArrow H (n : ℤ) (cyclicExtRepresentative c) := by
  unfold cyclicExtRepresentative
  rw [Ext.mapExactFunctor_hom]
  simp only [SpTowerClasses.mapSingleArrow, ShiftedHom.map, Category.assoc]

/-- An explicit functorial composite used by cyclic transport.
Source: coefficient changes (1), exact-single and shift comparisons.
(blueprint: def-diagonal-cyclic-functor-calculus). -/
@[irreducible] def threeFunctorArrowEquation
    {A₁ : Type a₁} [Category.{b₁} A₁] [Abelian A₁]
    {A₂ : Type a₂} [Category.{b₂} A₂] [Abelian A₂]
    {A₃ : Type a₃} [Category.{b₃} A₃] [Abelian A₃]
    {A₄ : Type a₄} [Category.{b₄} A₄] [Abelian A₄]
    [HasDerivedCategory.{d₁} A₁] [HasDerivedCategory.{d₂} A₂]
    [HasDerivedCategory.{d₃} A₃] [HasDerivedCategory.{d₄} A₄]
    (R : DerivedCategory A₁ ⥤ DerivedCategory A₂)
    (G : A₂ ⥤ A₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A₃ ⥤ A₄) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (n : ℕ) {X₁ Y₁ : A₁} {X₂ Y₂ : A₂} {X₃ Y₃ : A₃}
    (q : (DerivedCategory.singleFunctor A₂ 0).obj X₂ ⟶
      R.obj ((DerivedCategory.singleFunctor A₁ 0).obj X₁))
    (r : R.obj (((DerivedCategory.singleFunctor A₁ 0).obj Y₁)⟦(n : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor A₂ 0).obj Y₂)⟦(n : ℤ)⟧)
    (s : G.obj X₂ ≅ X₃) (t : G.obj Y₂ ≅ Y₃)
    (α : (DerivedCategory.singleFunctor A₁ 0).obj X₁ ⟶
      ((DerivedCategory.singleFunctor A₁ 0).obj Y₁)⟦(n : ℤ)⟧) : Prop :=
    SpTowerClasses.mapSingleArrow H (n : ℤ)
      ((DerivedCategory.singleFunctor A₃ 0).map s.inv ≫
        SpTowerClasses.mapSingleArrow G (n : ℤ) (q ≫ R.map α ≫ r) ≫
          ((DerivedCategory.singleFunctor A₃ 0).map t.hom)⟦(n : ℤ)⟧') =
      threeFunctorSource R G H q s ≫
        (R ⋙ G.mapDerivedCategory ⋙ H.mapDerivedCategory).map α ≫
        threeFunctorTarget R G H n r t

/-- The normalized three-functor equation.
Source: coefficient changes (1) (blueprint: def-diagonal-cyclic-functor-calculus).
Proof: expand the single-arrow maps and use functoriality and associativity. -/
theorem threeFunctorArrowCalculation
    {A₁ : Type a₁} [Category.{b₁} A₁] [Abelian A₁]
    {A₂ : Type a₂} [Category.{b₂} A₂] [Abelian A₂]
    {A₃ : Type a₃} [Category.{b₃} A₃] [Abelian A₃]
    {A₄ : Type a₄} [Category.{b₄} A₄] [Abelian A₄]
    [HasDerivedCategory.{d₁} A₁] [HasDerivedCategory.{d₂} A₂]
    [HasDerivedCategory.{d₃} A₃] [HasDerivedCategory.{d₄} A₄]
    (R : DerivedCategory A₁ ⥤ DerivedCategory A₂)
    (G : A₂ ⥤ A₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A₃ ⥤ A₄) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (n : ℕ) {X₁ Y₁ : A₁} {X₂ Y₂ : A₂} {X₃ Y₃ : A₃}
    (q : (DerivedCategory.singleFunctor A₂ 0).obj X₂ ⟶
      R.obj ((DerivedCategory.singleFunctor A₁ 0).obj X₁))
    (r : R.obj (((DerivedCategory.singleFunctor A₁ 0).obj Y₁)⟦(n : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor A₂ 0).obj Y₂)⟦(n : ℤ)⟧)
    (s : G.obj X₂ ≅ X₃) (t : G.obj Y₂ ≅ Y₃)
    (α : (DerivedCategory.singleFunctor A₁ 0).obj X₁ ⟶
      ((DerivedCategory.singleFunctor A₁ 0).obj Y₁)⟦(n : ℤ)⟧) :
    threeFunctorArrowEquation R G H n q r s t α := by
  unfold threeFunctorArrowEquation
  simp only [threeFunctorSource, threeFunctorTarget, SpTowerClasses.mapSingleArrow,
    Functor.map_comp, Functor.comp_map, Category.assoc]

/-- The three-functor equation for a supplied finite representative.
Source: coefficient changes (1) (blueprint: def-diagonal-cyclic-functor-calculus).
The body is an equality of explicit arrows; it asserts no equality by itself. -/
@[irreducible] def threeFunctorRepresentativeEquation
    {A₁ : Type a₁} [Category.{b₁} A₁] [Abelian A₁]
    {A₂ : Type a₂} [Category.{b₂} A₂] [Abelian A₂]
    {A₃ : Type a₃} [Category.{b₃} A₃] [Abelian A₃]
    {A₄ : Type a₄} [Category.{b₄} A₄] [Abelian A₄]
    [HasDerivedCategory.{d₁} A₁] [HasDerivedCategory.{d₂} A₂]
    [HasDerivedCategory.{d₃} A₃] [HasDerivedCategory.{d₄} A₄]
    (R : DerivedCategory A₁ ⥤ DerivedCategory A₂)
    (G : A₂ ⥤ A₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A₃ ⥤ A₄) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (n : ℕ) {X₁ Y₁ : A₁} {X₂ Y₂ : A₂} {X₃ Y₃ : A₃}
    (q : (DerivedCategory.singleFunctor A₂ 0).obj X₂ ⟶
      R.obj ((DerivedCategory.singleFunctor A₁ 0).obj X₁))
    (r : R.obj (((DerivedCategory.singleFunctor A₁ 0).obj Y₁)⟦(n : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor A₂ 0).obj Y₂)⟦(n : ℤ)⟧)
    (s : G.obj X₂ ≅ X₃) (t : G.obj Y₂ ≅ Y₃)
    (α : (DerivedCategory.singleFunctor A₁ 0).obj X₁ ⟶
      ((DerivedCategory.singleFunctor A₁ 0).obj Y₁)⟦(n : ℤ)⟧)
    (β : (DerivedCategory.singleFunctor A₃ 0).obj X₃ ⟶
      ((DerivedCategory.singleFunctor A₃ 0).obj Y₃)⟦(n : ℤ)⟧) : Prop :=
  SpTowerClasses.mapSingleArrow H (n : ℤ) β =
    threeFunctorSource R G H q s ≫
      (R ⋙ G.mapDerivedCategory ⋙ H.mapDerivedCategory).map α ≫
      threeFunctorTarget R G H n r t

/-- Transfer the normalized arrow calculation to an equal supplied representative.
Source: coefficient changes (1) (blueprint: def-diagonal-cyclic-functor-calculus).
Proof: map hβ by the exact single-arrow operation, then use the normalized
three-functor calculation and transitivity. -/
theorem threeFunctorRepresentativeCalculation
    {A₁ : Type a₁} [Category.{b₁} A₁] [Abelian A₁]
    {A₂ : Type a₂} [Category.{b₂} A₂] [Abelian A₂]
    {A₃ : Type a₃} [Category.{b₃} A₃] [Abelian A₃]
    {A₄ : Type a₄} [Category.{b₄} A₄] [Abelian A₄]
    [HasDerivedCategory.{d₁} A₁] [HasDerivedCategory.{d₂} A₂]
    [HasDerivedCategory.{d₃} A₃] [HasDerivedCategory.{d₄} A₄]
    (R : DerivedCategory A₁ ⥤ DerivedCategory A₂)
    (G : A₂ ⥤ A₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A₃ ⥤ A₄) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (n : ℕ) {X₁ Y₁ : A₁} {X₂ Y₂ : A₂} {X₃ Y₃ : A₃}
    (q : (DerivedCategory.singleFunctor A₂ 0).obj X₂ ⟶
      R.obj ((DerivedCategory.singleFunctor A₁ 0).obj X₁))
    (r : R.obj (((DerivedCategory.singleFunctor A₁ 0).obj Y₁)⟦(n : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor A₂ 0).obj Y₂)⟦(n : ℤ)⟧)
    (s : G.obj X₂ ≅ X₃) (t : G.obj Y₂ ≅ Y₃)
    (α : (DerivedCategory.singleFunctor A₁ 0).obj X₁ ⟶
      ((DerivedCategory.singleFunctor A₁ 0).obj Y₁)⟦(n : ℤ)⟧)
    (β : (DerivedCategory.singleFunctor A₃ 0).obj X₃ ⟶
      ((DerivedCategory.singleFunctor A₃ 0).obj Y₃)⟦(n : ℤ)⟧)
    (hβ : β = (DerivedCategory.singleFunctor A₃ 0).map s.inv ≫
      SpTowerClasses.mapSingleArrow G (n : ℤ) (q ≫ R.map α ≫ r) ≫
        ((DerivedCategory.singleFunctor A₃ 0).map t.hom)⟦(n : ℤ)⟧') :
    threeFunctorRepresentativeEquation R G H n q r s t α β := by
  unfold threeFunctorRepresentativeEquation
  have hn := threeFunctorArrowCalculation R G H n q r s t α
  unfold threeFunctorArrowEquation at hn
  exact (congrArg (SpTowerClasses.mapSingleArrow H (n : ℤ)) hβ).trans hn

/-- An explicit functorial composite used by cyclic transport.
Source: coefficient changes (1), exact-single and shift comparisons.
(blueprint: def-diagonal-cyclic-functor-calculus). -/
@[irreducible] def completedFunctorSource
    {A₀ : Type a₀} [Category.{b₀} A₀] [Abelian A₀]
    {A₁ : Type a₁} [Category.{b₁} A₁] [Abelian A₁]
    [HasDerivedCategory.{d₀} A₀] [HasDerivedCategory.{d₁} A₁]
    {B : Type*} [Category B]
    (F : A₀ ⥤ A₁) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory A₁ ⥤ B)
    {X₀ : A₀} {X₁ : A₁} {P : B}
    (s : F.obj X₀ ≅ X₁)
    (σ : P ⟶ K.obj ((DerivedCategory.singleFunctor A₁ 0).obj X₁)) :
    P ⟶ (F.mapDerivedCategory ⋙ K).obj
      ((DerivedCategory.singleFunctor A₀ 0).obj X₀) :=
  σ ≫ K.map ((DerivedCategory.singleFunctor A₁ 0).map s.inv ≫
    (F.mapDerivedCategorySingleFunctor 0).inv.app X₀)

/-- An explicit functorial composite used by cyclic transport.
Source: coefficient changes (1), exact-single and shift comparisons.
(blueprint: def-diagonal-cyclic-functor-calculus). -/
@[irreducible] def completedFunctorTarget
    {A₀ : Type a₀} [Category.{b₀} A₀] [Abelian A₀]
    {A₁ : Type a₁} [Category.{b₁} A₁] [Abelian A₁]
    [HasDerivedCategory.{d₀} A₀] [HasDerivedCategory.{d₁} A₁]
    {B : Type*} [Category B]
    (F : A₀ ⥤ A₁) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory A₁ ⥤ B)
    (n : ℕ) {Y₀ : A₀} {Y₁ : A₁} {Q : B}
    (t : F.obj Y₀ ≅ Y₁)
    (τ : K.obj (((DerivedCategory.singleFunctor A₁ 0).obj Y₁)⟦(n : ℤ)⟧) ⟶ Q) :
    (F.mapDerivedCategory ⋙ K).obj
      (((DerivedCategory.singleFunctor A₀ 0).obj Y₀)⟦(n : ℤ)⟧) ⟶ Q :=
  K.map ((F.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
    ((F.mapDerivedCategorySingleFunctor 0).hom.app Y₀)⟦(n : ℤ)⟧' ≫
    ((DerivedCategory.singleFunctor A₁ 0).map t.hom)⟦(n : ℤ)⟧') ≫ τ

/-- An explicit functorial composite used by cyclic transport.
Source: coefficient changes (1), exact-single and shift comparisons.
(blueprint: def-diagonal-cyclic-functor-calculus). -/
theorem completedFunctorCalculation
    {A₀ : Type a₀} [Category.{b₀} A₀] [Abelian A₀]
    {A₁ : Type a₁} [Category.{b₁} A₁] [Abelian A₁]
    [HasDerivedCategory.{d₀} A₀] [HasDerivedCategory.{d₁} A₁]
    {B : Type*} [Category B]
    (F : A₀ ⥤ A₁) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory A₁ ⥤ B)
    (n : ℕ) {X₀ Y₀ : A₀} {X₁ Y₁ : A₁} {P Q : B}
    (s : F.obj X₀ ≅ X₁) (t : F.obj Y₀ ≅ Y₁)
    (σ : P ⟶ K.obj ((DerivedCategory.singleFunctor A₁ 0).obj X₁))
    (τ : K.obj (((DerivedCategory.singleFunctor A₁ 0).obj Y₁)⟦(n : ℤ)⟧) ⟶ Q)
    (f : (DerivedCategory.singleFunctor A₀ 0).obj X₀ ⟶
      ((DerivedCategory.singleFunctor A₀ 0).obj Y₀)⟦(n : ℤ)⟧)
    (α : (DerivedCategory.singleFunctor A₁ 0).obj X₁ ⟶
      ((DerivedCategory.singleFunctor A₁ 0).obj Y₁)⟦(n : ℤ)⟧)
    (hα : (DerivedCategory.singleFunctor A₁ 0).map s.inv ≫
      SpTowerClasses.mapSingleArrow F (n : ℤ) f ≫
        ((DerivedCategory.singleFunctor A₁ 0).map t.hom)⟦(n : ℤ)⟧' = α)
    (d : P ⟶ Q) (hd : d = σ ≫ K.map α ≫ τ) :
    d = completedFunctorSource F K s σ ≫
      (F.mapDerivedCategory ⋙ K).map f ≫ completedFunctorTarget F K n t τ := by
  rw [hd, ← hα]
  simp only [completedFunctorSource, completedFunctorTarget, SpTowerClasses.mapSingleArrow,
    Functor.map_comp, Functor.comp_map, Category.assoc]

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
