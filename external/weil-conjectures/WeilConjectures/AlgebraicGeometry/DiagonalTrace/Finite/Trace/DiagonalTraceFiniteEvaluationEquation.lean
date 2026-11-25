/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteBoundaryMaps

/-! # The finite evaluation equation in fixed coordinates -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe wB wD
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- A finite Ext class realizes an evaluated derived arrow in the two supplied coordinates.
The definition is the explicit coordinate equation, with no chosen witnesses or extra data.
Source: exact single and shifted-single comparisons in diagonal trace proof (2).
(blueprint: def-sfb-diagonal-trace-finite-evaluation-equation). -/
@[irreducible] def finiteEvaluationEquation
    {C B D : Type*} [Category C] [Category B] [Category D]
    [Abelian C] [Abelian B] [Abelian D]
    [HasExt.{wB} B] [HasExt.{wD} D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    (F : C ⥤ (ℕᵒᵖ ⥤ D)) (S : B ⥤ D) [F.Additive] [S.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    {X Y : C} {P Q : B} (n : ℕ) (a : (F.obj X).obj (op n) ≅ S.obj P)
    (b : (F.obj Y).obj (op n) ≅ S.obj Q)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(2 : ℤ)⟧)
    (y : Ext.{wB} P Q 2) : Prop :=
  (y.mapExactFunctor S).hom = (supportedFiniteSingleCoordinates F X n a).inv ≫
    (((evaluation ℕᵒᵖ D).obj (op n)).mapDerivedCategory).map
      (F.mapDerivedCategory.map f) ≫
    (supportedFiniteShiftedCoordinates F Y n b).hom

end AlgebraicGeometry.ProEtale.DiagonalTrace
