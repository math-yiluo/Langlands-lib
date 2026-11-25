/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-!
# The derived extension of scalars is triangulated

For a morphism `φ : R ⟶ S` of commutative monoid objects in a Grothendieck abelian closed
symmetric monoidal category, the derived extension of scalars `L(Ext_φ)` is left adjoint to the
restriction of scalars `D(Res_φ)` on the derived categories
(`CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction`). The restriction of scalars is
exact, so `D(Res_φ)` is triangulated; this file equips `L(Ext_φ)` with the commutation with the
shifts for which the adjunction commutes with the shifts
(`CategoryTheory.Mod.commShift_leftDerivedExtendScalars`), for which `L(Ext_φ)` is triangulated
(`CategoryTheory.Mod.isTriangulated_leftDerivedExtendScalars`), as the left adjoint of a
triangulated functor.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- The derived extension of scalars commutes with the shifts, as the left adjoint of the
restriction of scalars `D(Res_φ)`. This is the structure for which the adjunction
`L(Ext_φ) ⊣ D(Res_φ)` commutes with the shifts. -/
noncomputable instance commShift_leftDerivedExtendScalars :
    (extendScalars φ).leftDerivedFunctor.CommShift ℤ :=
  (derivedExtendMapDerivedCategoryAdjunction φ).leftAdjointCommShift ℤ

instance commShift_derivedExtendMapDerivedCategoryAdjunction :
    (derivedExtendMapDerivedCategoryAdjunction φ).CommShift ℤ :=
  (derivedExtendMapDerivedCategoryAdjunction φ).commShift_of_rightAdjoint ℤ

/-- The derived extension of scalars is triangulated, as the left adjoint of the triangulated
restriction of scalars. -/
instance isTriangulated_leftDerivedExtendScalars :
    (extendScalars φ).leftDerivedFunctor.IsTriangulated :=
  (derivedExtendMapDerivedCategoryAdjunction φ).isTriangulated_leftAdjoint

end CategoryTheory.Mod
