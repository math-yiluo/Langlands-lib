/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Kummer.KummerStrictAdjunctData
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement

/-! # The compared Kummer boundary formula. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
attribute [local instance 11000] kummerAbHasExt kummerModuleHasExt
attribute [local irreducible] CategoryTheory.Abelian.Ext DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  comparisonUpperStar cartierProRootMap cartierProKummerUnit cartierUnitsComparison
  cartierRootsIso cartierRootsComparison
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension diagonalScalarAdjunction

private theorem mk0_ext_mk0_hom
    {A : Type*} [Category A] [Abelian A] [HasExt.{w} A] [HasDerivedCategory.{w} A]
    {X Y Z P : A} (a : X ⟶ Y) (β : Ext Y Z 1) (r : Z ⟶ P) :
    ((Ext.mk₀ a).comp (β.comp (Ext.mk₀ r) (add_zero 1)) (zero_add 1)).hom =
      (DerivedCategory.singleFunctor A 0).map a ≫ β.hom ≫
        ((DerivedCategory.singleFunctor A 0).map r)⟦(1 : ℤ)⟧' := by
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  rfl

/-- Expand the compared Kummer class as its actual short-exact-sequence boundary. -/
theorem kummer_compared_boundary_formula (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)] (n : ℕ) :
    let F := DerivedCategory.singleFunctor (DiagonalAb W) 0
    let hS := cartierProKummer_exact W (ℓ ^ (n + 1))
      (pow_pos (Fact.out : ℓ.Prime).pos _) (by simpa using hW.pow (n + 1))
    let δ : F.obj (Scheme.proEtaleUnitsSheaf W) ⟶
        (F.obj (Scheme.proEtaleRootsOfUnitySheaf W (ℓ ^ (n + 1))))⟦(1 : ℤ)⟧ := hS.singleδ
    (kummerComparedUnit ℓ W hW n).hom = F.map (cartierUnitsComparison W) ≫ δ ≫
      (F.map (cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) W (pow_pos (Fact.out : ℓ.Prime).pos _)
        (by simpa using hW.pow (n + 1))))⟦(1 : ℤ)⟧' := by
  let F := DerivedCategory.singleFunctor (DiagonalAb W) 0
  let hS := cartierProKummer_exact W (ℓ ^ (n + 1))
    (pow_pos (Fact.out : ℓ.Prime).pos _) (by simpa using hW.pow (n + 1))
  let β : Ext (Scheme.proEtaleUnitsSheaf W)
      (Scheme.proEtaleRootsOfUnitySheaf W (ℓ ^ (n + 1))) 1 := hS.extClass
  have hb : β.hom = hS.singleδ := hS.extClass_hom
  unfold kummerComparedUnit cartierProKummerUnit cartierKummerClass
  change ((Ext.mk₀ (cartierUnitsComparison W)).comp
    (β.comp (Ext.mk₀ (cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) W (pow_pos (Fact.out : ℓ.Prime).pos _)
      (by simpa using hW.pow (n + 1)))) (add_zero 1)) (zero_add 1)).hom = _
  exact (mk0_ext_mk0_hom _ β _).trans (by rw [hb]; rfl)

end AlgebraicGeometry.ProEtale
