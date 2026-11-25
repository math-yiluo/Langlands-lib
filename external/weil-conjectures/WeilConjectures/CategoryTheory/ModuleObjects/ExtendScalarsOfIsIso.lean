/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit

/-!
# Extension of scalars along an isomorphism, on underlying objects

Let `φ : R ⟶ S` be an isomorphism of algebra objects, `R` commutative. Extension of scalars
`Ext_φ` along `φ` is restriction of scalars along `φ⁻¹` (`Mod.extendScalarsIsoComapInv`), and
restriction of scalars along `φ` is an equivalence (`Mod.comapEquivalenceOfIsIso`). This file
computes, on underlying objects, the maps `Ext_φ M ⟶ N` obtained from maps `M ⟶ Res_φ N` through
these identifications: precomposed with the unit `M ⟶ S ⊗_R M` of the extension of scalars,
they are the original maps.

## Main results

- `CategoryTheory.Mod.hom_ext_of_extendUnitHom`: maps out of `S ⊗_R M` are determined by their
  precomposition with the unit `M ⟶ S ⊗_R M`.
- `CategoryTheory.Mod.extendUnitHom_comp_extendScalars_map_comp_hom`: the map
  `Ext_φ M ⟶ Ext_φ Res_φ N ≅ Res_{φ⁻¹} Res_φ N ≅ N` induced by `g : M ⟶ Res_φ N`, precomposed
  with the unit, is `g`.
- `CategoryTheory.Mod.extendUnitHom_comp_compIsoOfIsIso_hom_app_hom`,
  `CategoryTheory.Mod.extendUnitHom_comp_isoIdOfIsIso_hom_app_hom`: the same statement for the
  natural isomorphisms `P ⋙ G ⋙ Ext_φ ≅ P'` and `G ⋙ Ext_φ ≅ 𝟭` induced by isomorphisms
  `P ⋙ G ≅ P' ⋙ Res_φ` and `G ≅ Res_φ`.
-/

@[expose] public section

universe v₁ u₁

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [BraidedCategory C] {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

/-- Two maps `S ⊗_R M ⟶ N` of `S`-modules agreeing after precomposition with the unit
`M ⟶ S ⊗_R M` are equal. -/
lemma hom_ext_of_extendUnitHom {M : Mod C R} {N : Mod C S} {g g' : extendScalarsObj φ M ⟶ N}
    (h : extendUnitHom φ M ≫ g.hom = extendUnitHom φ M ≫ g'.hom) : g = g' := by
  refine (extendHomEquiv φ M N).injective (Mod.hom_ext _ _ ?_)
  simpa [extendHomEquiv] using h

/-- The unit `M ⟶ S ⊗_R M` is natural on underlying objects. -/
@[reassoc]
lemma extendUnitHom_comp_extendScalars_map_hom {M M' : Mod C R} (g : M ⟶ M') :
    extendUnitHom φ M ≫ ((extendScalars φ).map g).hom = g.hom ≫ extendUnitHom φ M' := by
  have hn := congrArg Mod.Hom.hom ((extendRestrictAdjunction φ).unit.naturality g)
  simp only [Functor.id_map, Functor.comp_map, Mod.comp_hom', Mod.comap_map_hom,
    extendRestrictAdjunction_unit_app_hom] at hn
  exact hn.symm

variable [IsIso φ]

/-- The unit `M ⟶ S ⊗_R M` of the extension of scalars along the isomorphism `φ`, followed by
the identification `Ext_φ ≅ Res_{φ⁻¹}`, is the identity of the underlying object. -/
@[reassoc]
lemma extendUnitHom_extendScalarsIsoComapInv_hom_app_hom (M : Mod C R) :
    extendUnitHom φ M ≫ ((extendScalarsIsoComapInv φ).hom.app M).hom = 𝟙 _ := by
  have h := congrArg Mod.Hom.hom (Adjunction.homEquiv_leftAdjointUniq_hom_app
    (extendRestrictAdjunction φ) (comapEquivalenceOfIsIso φ).symm.toAdjunction M)
  rw [Adjunction.homEquiv_unit, Mod.comp_hom', extendRestrictAdjunction_unit_app_hom,
    Mod.comap_map_hom] at h
  refine h.trans ?_
  simp [comapEquivalenceOfIsIso, comapCongr, Equivalence.mk, Equivalence.symm, comap]

/-- The map `Ext_φ M ⟶ Ext_φ Res_φ N ≅ Res_{φ⁻¹} Res_φ N ≅ N` induced by `g : M ⟶ Res_φ N`,
precomposed with the unit `M ⟶ S ⊗_R M`, is `g` on underlying objects. -/
lemma extendUnitHom_comp_extendScalars_map_comp_hom {M : Mod C R} {N : Mod C S}
    (g : M ⟶ (comap φ).obj N) :
    extendUnitHom φ M ≫ ((extendScalars φ).map g ≫ (extendScalarsIsoComapInv φ).hom.app _ ≫
      (comapEquivalenceOfIsIso φ).unitIso.inv.app N).hom = g.hom := by
  rw [Mod.comp_hom', Mod.comp_hom', extendUnitHom_comp_extendScalars_map_hom_assoc,
    extendUnitHom_extendScalarsIsoComapInv_hom_app_hom_assoc,
    comapEquivalenceOfIsIso_unitIso_inv_app_hom]
  exact Category.comp_id _

variable {A B : Type*} [Category A] [Category B]

/-- Let `P : A ⥤ B`, `G : B ⥤ Mod_R` and `P' : A ⥤ Mod_S` with an isomorphism
`m : P ⋙ G ≅ P' ⋙ Res_φ`. The induced isomorphism
`P ⋙ G ⋙ Ext_φ ≅ P' ⋙ Res_φ ⋙ Ext_φ ≅ P' ⋙ Res_φ ⋙ Res_{φ⁻¹} ≅ P'`, precomposed with the unit
`G (P a) ⟶ S ⊗_R G (P a)`, is `m` on underlying objects. -/
lemma extendUnitHom_comp_compIsoOfIsIso_hom_app_hom {P : A ⥤ B} {G : B ⥤ Mod C R}
    {P' : A ⥤ Mod C S} (m : P ⋙ G ≅ P' ⋙ comap φ) (a : A) :
    extendUnitHom φ (G.obj (P.obj a)) ≫ (((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight m (extendScalars φ) ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft P' (Functor.isoWhiskerLeft (comap φ) (extendScalarsIsoComapInv φ) ≪≫
        (comapEquivalenceOfIsIso φ).unitIso.symm) ≪≫ Functor.rightUnitor _).hom.app a).hom =
      (m.hom.app a).hom := by
  rw [← extendUnitHom_comp_extendScalars_map_comp_hom φ (m.hom.app a)]
  simp

/-- Let `G : B ⥤ Mod_R` with an isomorphism `m : G ≅ Res_φ`. The induced isomorphism
`G ⋙ Ext_φ ≅ Res_φ ⋙ Ext_φ ≅ Res_φ ⋙ Res_{φ⁻¹} ≅ 𝟭`, precomposed with the unit
`G N ⟶ S ⊗_R G N`, is `m` on underlying objects. -/
lemma extendUnitHom_comp_isoIdOfIsIso_hom_app_hom {G : Mod C S ⥤ Mod C R}
    (m : G ≅ comap φ) (N : Mod C S) :
    extendUnitHom φ (G.obj N) ≫ ((Functor.isoWhiskerRight m (extendScalars φ) ≪≫
      Functor.isoWhiskerLeft (comap φ) (extendScalarsIsoComapInv φ) ≪≫
        (comapEquivalenceOfIsIso φ).unitIso.symm).hom.app N).hom = (m.hom.app N).hom := by
  rw [← extendUnitHom_comp_extendScalars_map_comp_hom φ (m.hom.app N)]
  simp

end CategoryTheory.Mod
