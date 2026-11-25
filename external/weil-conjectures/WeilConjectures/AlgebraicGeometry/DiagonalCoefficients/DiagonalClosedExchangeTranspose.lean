/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The direct-image transpose of a closed exchange -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem conjugate_transpose
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) {c : C} {d : D} (e : L₁.obj c ⟶ d) :
    a₁.homEquiv c d e ≫ (conjugateEquiv a₁ a₂ α).app d =
      a₂.homEquiv c d (α.app c ≫ e) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
    (conjugateEquiv a₁ a₂ α).naturality e, ← Category.assoc, unit_conjugateEquiv,
    Functor.map_comp, Category.assoc]

/-- Transpose an exchange around the other side of its adjoint square.

Source: blueprint latest, diagonal coefficient changes (3), closed-source exchange.
(blueprint: lem-diagonal-closed-exchange-transpose).

Proof: the conjugate identity moves the square comparison across the composite
adjunction. Naturality transposes the pulled closed counit, and the closed
adjunction triangle cancels that counit. What remains is closed direct image of
the transpose of the endpoint, followed by the direct-image square comparison.
This is purely categorical and needs no exactness or base-change invertibility. -/
theorem diagonalClosedExchange_transpose
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {I : B ⥤ A} {RI : A ⥤ B} {W : A ⥤ C} {RW : C ⥤ A}
    {V : B ⥤ D} {RV : D ⥤ B} {J : D ⥤ C} {RJ : C ⥤ D}
    (aI : I ⊣ RI) (aW : W ⊣ RW) (aV : V ⊣ RV) (aJ : J ⊣ RJ)
    (s : V ⋙ J ≅ I ⋙ W) (d : RW ⋙ RI ≅ RJ ⋙ RV)
    (hs : conjugateEquiv (aI.comp aW) (aV.comp aJ) s.hom = d.hom)
    (M : A) (N : C) (c : W.obj M ⟶ N) :
    aV.homEquiv _ _ (aJ.homEquiv _ _
        (s.hom.app (RI.obj M) ≫
          W.map (aI.counit.app M) ≫ c)) =
      RI.map (aW.homEquiv _ _ c) ≫ d.hom.app N := by
  have h := conjugate_transpose (aI.comp aW) (aV.comp aJ) s.hom
    (W.map (aI.counit.app M) ≫ c)
  rw [hs] at h
  have h' : aI.homEquiv _ _ (aW.homEquiv _ _ (W.map (aI.counit.app M) ≫ c)) ≫
      d.hom.app N =
      aV.homEquiv _ _ (aJ.homEquiv _ _
        (s.hom.app (RI.obj M) ≫ W.map (aI.counit.app M) ≫ c)) := by
    simpa only [Adjunction.comp_homEquiv, Equiv.trans_apply] using! h
  rw [← h']
  congr 1
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Adjunction.homEquiv_unit, aI.right_triangle_components,
    Category.id_comp, Functor.id_obj]

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
