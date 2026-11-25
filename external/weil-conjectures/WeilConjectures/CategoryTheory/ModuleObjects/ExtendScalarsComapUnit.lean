/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit

/-!
# Extension of scalars along isomorphisms and the units of extension of scalars

For a commutative square `a ≫ ψ = φ ≫ b` of morphisms of algebra objects with `a` and `b`
isomorphisms, the isomorphism `Ext_b ⋙ Res_ψ ≅ Res_φ ⋙ Ext_a`
(`CategoryTheory.Mod.extendScalarsComapIsoOfIsIso`) is compatible with the units
`M ⟶ Ext M` of the adjunctions between extension and restriction of scalars
(`Mod.extendRestrictAdjunction_unit_app_hom_extendScalarsComapIsoOfIsIso_inv_app_hom`).
-/

@[expose] public section

universe v₁ u₁

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [BraidedCategory C]

/-- The inverse of the identification of extension of scalars along an isomorphism `φ` with
restriction of scalars along `φ⁻¹` is the unit of extension of scalars on underlying objects. -/
lemma extendScalarsIsoComapInv_inv_app_hom
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    (M : Mod C R) :
    ((extendScalarsIsoComapInv φ).inv.app M).hom =
      ((extendRestrictAdjunction φ).unit.app M).hom := by
  have h := extendUnitHom_extendScalarsIsoComapInv_hom_app φ M
  have h' := congrArg Mod.Hom.hom ((extendScalarsIsoComapInv φ).hom_inv_id_app M)
  simp only [Mod.comp_hom', Mod.id_hom'] at h'
  rw [extendRestrictAdjunction_unit_app_hom]
  calc ((extendScalarsIsoComapInv φ).inv.app M).hom
      = (extendUnitHom φ M ≫ ((extendScalarsIsoComapInv φ).hom.app M).hom) ≫
          ((extendScalarsIsoComapInv φ).inv.app M).hom := by
        rw [h]
        exact (Category.id_comp _).symm
    _ = extendUnitHom φ M := by
        rw [Category.assoc, h']
        exact Category.comp_id _

variable {R S R' S' : C} [MonObj R] [MonObj S] [MonObj R'] [MonObj S'] [IsCommMonObj R]
  [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ] (ψ : R' ⟶ S') [IsMonHom ψ]
  (a : R ⟶ R') [IsMonHom a] [IsIso a] (b : S ⟶ S') [IsMonHom b] [IsIso b]
  (sq : a ≫ ψ = φ ≫ b)

/-- The isomorphism `Ext_b ⋙ Res_ψ ≅ Res_φ ⋙ Ext_a` of a commutative square `a ≫ ψ = φ ≫ b`
with `a` and `b` isomorphisms is compatible with the units of extension of scalars. -/
lemma extendRestrictAdjunction_unit_app_hom_extendScalarsComapIsoOfIsIso_inv_app_hom
    (M : Mod C S) :
    ((extendRestrictAdjunction a).unit.app ((comap φ).obj M)).hom ≫
      ((extendScalarsComapIsoOfIsIso φ ψ a b sq).inv.app M).hom =
      ((extendRestrictAdjunction b).unit.app M).hom := by
  have ha := extendUnitHom_extendScalarsIsoComapInv_hom_app a ((comap φ).obj M)
  simp only [extendScalarsComapIsoOfIsIso, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Iso.symm_inv, Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, comp_hom', comap_map_hom, extendScalarsIsoComapInv_inv_app_hom,
    extendRestrictAdjunction_unit_app_hom, comapComp_hom_app_hom, comapComp_inv_app_hom,
    comapCongr_inv_app_hom, Functor.comp_obj]
  erw [Category.comp_id, Category.comp_id, Category.comp_id, reassoc_of% ha]

end CategoryTheory.Mod
