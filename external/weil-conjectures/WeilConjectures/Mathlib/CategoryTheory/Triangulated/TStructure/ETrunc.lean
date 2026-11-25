/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc

/-!
# Complements on the truncation functors indexed by `EInt`

We record extensionality principles for morphisms to `t.eTruncLT.obj b` and from
`t.eTruncGE.obj a`, and the compatibility of the commutation isomorphism
`t.eTruncLTGEIsoGELT a b` with the projections `t.eTruncGEπ a`.
-/

@[expose] public section

namespace CategoryTheory.Triangulated.TStructure

open Limits Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)

/-- Morphisms `W ⟶ t.eTruncLT.obj b Z` are determined by their composition with the
truncation morphism when `W` is `< b`, i.e. when `(t.eTruncLTι b).app W` is an isomorphism. -/
lemma to_eTruncLT_obj_ext {b : EInt} {W Z : C} {f₁ f₂ : W ⟶ (t.eTruncLT.obj b).obj Z}
    [IsIso ((t.eTruncLTι b).app W)]
    (h : f₁ ≫ (t.eTruncLTι b).app Z = f₂ ≫ (t.eTruncLTι b).app Z) : f₁ = f₂ := by
  have (f : W ⟶ (t.eTruncLT.obj b).obj Z) :
      f = inv ((t.eTruncLTι b).app W) ≫ (t.eTruncLT.obj b).map (f ≫ (t.eTruncLTι b).app Z) := by
    rw [IsIso.eq_inv_comp, Functor.map_comp, t.eTruncLT_obj_map_eTruncLTι_app]
    exact ((t.eTruncLTι b).naturality f).symm
  rw [this f₁, this f₂, h]

/-- Morphisms `t.eTruncGE.obj a Z ⟶ W` are determined by their precomposition with the
truncation morphism when `W` is `≥ a`, i.e. when `(t.eTruncGEπ a).app W` is an isomorphism. -/
lemma from_eTruncGE_obj_ext {a : EInt} {W Z : C} {f₁ f₂ : (t.eTruncGE.obj a).obj Z ⟶ W}
    [IsIso ((t.eTruncGEπ a).app W)]
    (h : (t.eTruncGEπ a).app Z ≫ f₁ = (t.eTruncGEπ a).app Z ≫ f₂) : f₁ = f₂ := by
  have (f : (t.eTruncGE.obj a).obj Z ⟶ W) :
      f = (t.eTruncGE.obj a).map ((t.eTruncGEπ a).app Z ≫ f) ≫ inv ((t.eTruncGEπ a).app W) := by
    rw [IsIso.eq_comp_inv, Functor.map_comp, t.eTruncGE_obj_map_eTruncGEπ_app]
    exact (t.eTruncGEπ a).naturality f
  rw [this f₁, this f₂, h]

variable [IsTriangulated C]

/-- The commutation isomorphism `τ_{< b} τ_{≥ a} ≅ τ_{≥ a} τ_{< b}` is compatible with the
projections `X ⟶ τ_{≥ a} X`. -/
@[reassoc (attr := simp)]
lemma eTruncLT_map_eTruncGEπ_app_eTruncLTGEIsoGELT_hom_app (a b : EInt) (X : C) :
    (t.eTruncLT.obj b).map ((t.eTruncGEπ a).app X) ≫ (t.eTruncLTGEIsoGELT a b).hom.app X =
      (t.eTruncGEπ a).app ((t.eTruncLT.obj b).obj X) := by
  rw [← Iso.app_hom, ← Iso.eq_comp_inv]
  apply t.to_eTruncLT_obj_ext
  have h : (t.eTruncLTGEIsoGELT a b).inv.app X ≫ (t.eTruncLTι b).app ((t.eTruncGE.obj a).obj X) =
      (t.eTruncGE.obj a).map ((t.eTruncLTι b).app X) := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, t.eTruncLTGEIsoGELT_hom_app_fac']
  rw [Category.assoc, Iso.app_inv, h, t.eTruncGEπ_naturality]
  exact (t.eTruncLTι b).naturality _

end CategoryTheory.Triangulated.TStructure
