/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
public import WeilConjectures.CategoryTheory.Ringed.RingedConstantTowerPushforwardNormalization
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Elementary comparison functors for the completed diagonal

Source: blueprint coefficient changes (3), exact pullback and constant/limit mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u a b c d va vb vc vd wa wb wc wd
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace

/-- The actual exact pullback, its termwise tower functor, the normalized
constant/limit mate, and exact localization of a comparison square.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-comparison-functors).
Construction: termwise application is whiskering right. Transpose the canonical
constant-tower interchange under the specified adjunctions. Localize an exact
square by the two canonical composition comparisons and its natural isomorphism. -/
abbrev diagonalClassPull (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S] :
    DiagonalMod l S ⥤ DiagonalMod l X :=
  upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f

/-- Its strict termwise tower functor.
Source: blueprint coefficient proof (3)
(blueprint: def-diagonal-class-comparison-functors). -/
abbrev diagonalClassTowerPull (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S] :
    DiagonalSystems l S ⥤ DiagonalSystems l X :=
  (Functor.whiskeringRight ℕᵒᵖ (DiagonalMod l S) (DiagonalMod l X)).obj
    (diagonalClassPull l f)

/-- Transpose the canonical constant-tower interchange under the specified adjunctions.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-comparison-functors). -/
def diagonalClassLimitMate (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (LX : DiagonalRlim (DiagonalMod l X)) (LS : DiagonalRlim (DiagonalMod l S))
    (adjX : (Functor.const ℕᵒᵖ : DiagonalMod l X ⥤ DiagonalSystems l X).mapDerivedCategory ⊣ LX.R)
    (adjS : (Functor.const ℕᵒᵖ : DiagonalMod l S ⥤ DiagonalSystems l S).mapDerivedCategory ⊣ LS.R) :
    LS.R ⋙ (diagonalClassPull l f).mapDerivedCategory ⟶
      (diagonalClassTowerPull l f).mapDerivedCategory ⋙ LX.R :=
  (mateEquiv adjS adjX (TwoSquare.mk _ _ _ _
    (ringedConstantTowerPullback (diagonalClassPull l f)).inv))

/-- Localize an exact comparison square using the canonical composition isomorphisms.
Source: blueprint coefficient changes (3)
(blueprint: def-diagonal-class-comparison-functors). -/
def diagonalClassExactSquare
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wd} D]
    (U : A ⥤ B) (F : B ⥤ D) (G : A ⥤ C) (V : C ⥤ D)
    [U.Additive] [F.Additive] [G.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (s : U ⋙ F ≅ G ⋙ V) :
    U.mapDerivedCategory ⋙ F.mapDerivedCategory ≅
      G.mapDerivedCategory ⋙ V.mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso U F ≪≫
    Functor.mapDerivedCategoryNatIso s ≪≫ (Functor.mapDerivedCategoryCompIso G V).symm

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
