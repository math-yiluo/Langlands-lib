/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! # The ordinary restriction comparison and adjunction mates -/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance instEssentiallySmallProfinite_comapUpperStarIsoMate
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

private lemma extendUnitHom_isoComapInv
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
    [∀ W : C, PreservesColimitsOfSize.{0, 0} (tensorLeft W)]
    [∀ W : C, PreservesColimitsOfSize.{0, 0} (tensorRight W)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] (M : Mod C R) :
    Mod.extendUnitHom φ M ≫ ((Mod.extendScalarsIsoComapInv φ).hom.app M).hom = 𝟙 M.X := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (Mod.extendRestrictAdjunction φ) (Mod.comapEquivalenceOfIsIso φ).symm.toAdjunction M
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg Mod.Hom.hom h
  simpa [Mod.extendScalarsIsoComapInv, Mod.comapEquivalenceOfIsIso,
    Mod.extendRestrictAdjunction, Adjunction.mkOfHomEquiv_unit_app,
    CategoryTheory.Equivalence.counitInv, CategoryTheory.Equivalence.mk,
    Mod.comapComp, Mod.comapId, Mod.comapCongr] using hh

private lemma isoComapInv_inv_hom
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
    [∀ W : C, PreservesColimitsOfSize.{0, 0} (tensorLeft W)]
    [∀ W : C, PreservesColimitsOfSize.{0, 0} (tensorRight W)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] (M : Mod C R) :
    ((Mod.extendScalarsIsoComapInv φ).inv.app M).hom = Mod.extendUnitHom φ M := by
  have h := congrArg (fun k ↦ k ≫ ((Mod.extendScalarsIsoComapInv φ).inv.app M).hom)
    (extendUnitHom_isoComapInv φ M)
  have hc := congrArg Mod.Hom.hom (Iso.hom_inv_id_app (Mod.extendScalarsIsoComapInv φ) M)
  simp only [Mod.comp_hom', Mod.id_hom'] at hc
  rw [Category.assoc, hc] at h
  erw [Category.comp_id, Category.id_comp] at h
  exact h.symm

private lemma ofNatIsoRight_unit_app {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (e : G ≅ H) (x : C) :
    (adj.ofNatIsoRight e).unit.app x = adj.unit.app x ≫ e.hom.app _ := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_id]

omit [IsCommMonObj Λ'] [MonObj Λ'] [IsMonHom a] in
private lemma pull_unit_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    ((upperStarLowerStarAdjunction Λ f).unit.app M).hom =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app M.X ≫
        (f)_*[Ab.{u + 1}].map
          (Mod.extendUnitHom (condensedPullbackHom Λ f)
            (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj M)) := by
  simp only [upperStarLowerStarAdjunction, ofNatIsoRight_unit_app,
    Adjunction.comp_unit_app, Mod.comp_hom', Adjunction.mapModAdjunction_unit_app_hom]
  simp [comapPullbackHomCompIso, Mod.extendRestrictAdjunction,
    Adjunction.mkOfHomEquiv_unit_app, Mod.extendHomEquiv]

private lemma comapUpperStarIso_inv_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ' Y)) :
    ((comapUpperStarIso a f).inv.app N).hom =
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom.app
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj
          ((Mod.comap (coefficientMap a Y)).obj N))).hom ≫
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ' f)).inv.app
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ' Y)).obj N)).hom := by
  have hn := congrArg Mod.Hom.hom
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom.naturality
      (((f)^*[Ab.{u + 1}].mapModComapIso (coefficientMap a Y)).hom.app N))
  simp only [Mod.comp_hom', Mod.comap_map_hom,
    Functor.mapModComapIso_hom_app_hom] at hn
  simp only [Functor.comp_obj, Mod.comap_obj_X, comapUpperStarIso,
    Mod.extendScalarsComapIsoOfIsIso, asIso_inv, Mod.comapComp, Mod.comapCongr,
    Functor.isoWhiskerLeft_trans, Functor.isoWhiskerLeft_twice, Functor.mapModComapIso,
    Functor.mapMod_obj_X, Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.trans_inv,
    Functor.isoWhiskerRight_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv, Category.assoc,
    NatTrans.comp_app, Mod.extendScalars_obj, Functor.associator_inv_app,
    Functor.whiskerRight_app, NatIso.ofComponents_hom_app, Mod.extendScalars_map,
    Functor.whiskerLeft_app, Functor.associator_hom_app, NatIso.ofComponents_inv_app,
    Category.comp_id, Category.id_comp, Mod.comp_hom', Mod.id_hom', Mod.isoMk_inv_hom,
    Iso.refl_inv, Mod.isoMk_hom_hom, Iso.refl_hom, Mod.comap_map_hom]
  erw [Category.id_comp]
  erw [Category.comp_id] at hn
  have hh := congrArg (fun k ↦ k ≫
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ' f)).inv.app
        (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ' Y)).obj N)).hom) hn
  simpa [Functor.mapModComapIso, Mod.extendScalars, upperStar] using hh

-- Normalization uses the module adjunctions and scalar extension uniqueness.
/-- The canonical restriction/pullback comparison is the inverse mate of the
restriction/pushforward comparison for one scheme map.
Source: Bhatt--Scholze, Remark 6.8.15, and the explicit constructions in
`ModuleObject.ChangeOfCoefficients` and `ModuleObject.UpperLowerStar.Defs`.
(auxiliary; not a blueprint node)

Proof. Expand the module pull/push adjunction as the composite of the lifted
monoidal sheaf adjunction and extension/restriction along the coefficient-pullback
isomorphism. Extension along this isomorphism is restriction along its inverse;
the unit of their adjunction is the resulting identification of the actions.
The coefficient square commutes by naturality of upperStarFromPointComp. Thus
restriction of the pullback unit, followed by the identity underlying
restriction/pushforward comparison, equals the pullback unit of the restricted
module followed by pushforward of the inverse restriction/pullback comparison.
Transpose this unit equation. The triangle identity and faithfulness of the module
forgetful functor identify its mate with comapLowerStarIso. This argument is for
one map only and uses neither composition coherence nor flatness of a. -/
theorem comapUpperStarIso_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    mateEquiv (upperStarLowerStarAdjunction Λ' f) (upperStarLowerStarAdjunction Λ f)
      (TwoSquare.mk _ _ _ _ (comapUpperStarIso a f).inv) =
      TwoSquare.mk _ _ _ _ (comapLowerStarIso a f).hom := by
  have hu (N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ' Y)) :
      (Mod.comap (coefficientMap a Y)).map
          ((upperStarLowerStarAdjunction Λ' f).unit.app N) ≫
        (comapLowerStarIso a f).hom.app ((f)^*⟦Λ'⟧.obj N) =
      (upperStarLowerStarAdjunction Λ f).unit.app
          ((Mod.comap (coefficientMap a Y)).obj N) ≫
        (f)_*⟦Λ⟧.map ((comapUpperStarIso a f).inv.app N) := by
    apply Mod.hom_ext
    change ((upperStarLowerStarAdjunction Λ' f).unit.app N).hom ≫
        ((comapLowerStarIso a f).hom.app ((f)^*⟦Λ'⟧.obj N)).hom =
      ((upperStarLowerStarAdjunction Λ f).unit.app
        ((Mod.comap (coefficientMap a Y)).obj N)).hom ≫
        (f)_*[Ab.{u + 1}].map (((comapUpperStarIso a f).inv.app N).hom)
    simp only [comapLowerStarIso, Mod.comapMapModComapIso_hom_app_hom,
      pull_unit_hom, comapUpperStarIso_inv_hom]
    erw [Category.comp_id]
    rw [Category.assoc, ← (f)_*[Ab.{u + 1}].map_comp]
    rw [← Category.assoc, extendUnitHom_isoComapInv]
    erw [Category.id_comp]
    rw [isoComapInv_inv_hom]
    rfl
  apply (mateEquiv (upperStarLowerStarAdjunction Λ' f)
    (upperStarLowerStarAdjunction Λ f)).symm.injective
  simp only [Equiv.symm_apply_apply]
  refine NatTrans.ext (funext fun N ↦ ?_)
  apply ((upperStarLowerStarAdjunction Λ f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact (hu N).symm.trans (unit_mateEquiv_symm
    (upperStarLowerStarAdjunction Λ' f) (upperStarLowerStarAdjunction Λ f)
    (TwoSquare.mk _ _ _ _ (comapLowerStarIso a f).hom) N)

end AlgebraicGeometry.ProEtale.CondensedRing
