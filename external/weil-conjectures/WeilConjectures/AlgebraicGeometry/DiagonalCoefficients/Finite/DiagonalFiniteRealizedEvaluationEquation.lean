/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicFunctorCalculus

/-! # Equations used in cyclic transport

These proposition wrappers have exactly the original equation bodies. Their
irreducibility keeps existential proof motives small during kernel checking.
Source: diagonal tower coefficient changes (1).
(blueprint: def-diagonal-finite-realized-evaluation-equation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a₁ b₁ d₁ a₄ b₄ d₄ w₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 5000] cyclicSmallShiftedSingleHom

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  Functor.mapDerivedCategory shiftFunctor geoCartierConstant geoCartierLine

/-- The finite-realization and exact-restriction equation at generic coefficients.
Source: coefficient changes (1)
(blueprint: def-diagonal-finite-realized-evaluation-equation).
The definition is a literal representative equation and chooses no object. -/
@[irreducible] def finiteRealizedEvaluationEquation
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {A : Type (u + 1)} [CommRing A]
    {A₁ : Type a₁} [Category.{b₁} A₁] [Abelian A₁] [HasDerivedCategory.{d₁} A₁]
    {B : Type a₄} [Category.{b₄} B] [Abelian B]
    [dB : HasDerivedCategory.{d₄} B] [eB : HasExt.{w₂} B]
    (N : ℕ) (hA : (N : A) = 0) (Y : Scheme.{u})
    {L : ∀ X : Scheme.{u}, Modules R X}
    (eW : FiniteRealization R A (diagonalSurface Y))
    (line : eW.F.obj (L (diagonalSurface Y)) ≅ geoCartierLine A N hA (diagonalSurface Y))
    (s : eW.F.obj (source R Y) ≅
      (lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
        (geoCartierConstant A (ProjectiveLine Y)))
    (R₀ : DerivedCategory A₁ ⥤ DerivedCategory (Modules R (diagonalSurface Y)))
    (H : Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) (ModuleCat.{u + 1} A) ⥤ B)
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {X₁ Y₁ : A₁}
    (q : (DerivedCategory.singleFunctor _ 0).obj (source R Y) ⟶
      R₀.obj ((DerivedCategory.singleFunctor A₁ 0).obj X₁))
    (r : R₀.obj (((DerivedCategory.singleFunctor A₁ 0).obj Y₁)⟦(2 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj (L (diagonalSurface Y)))⟦(2 : ℤ)⟧)
    (α : (DerivedCategory.singleFunctor A₁ 0).obj X₁ ⟶
      ((DerivedCategory.singleFunctor A₁ 0).obj Y₁)⟦(2 : ℤ)⟧) : Prop :=
  cyclicExtRepresentative
    ((finiteRealizedClass N hA Y eW line s (q ≫ R₀.map α ≫ r)).mapExactFunctor H :
      Ext.{w₂} (H.obj ((lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
        (geoCartierConstant A (ProjectiveLine Y))))
        (H.obj (geoCartierLine A N hA (diagonalSurface Y))) 2) =
    threeFunctorSource R₀ eW.F H q s ≫
      (R₀ ⋙ eW.F.mapDerivedCategory ⋙ H.mapDerivedCategory).map α ≫
      threeFunctorTarget R₀ eW.F H 2 r line

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
