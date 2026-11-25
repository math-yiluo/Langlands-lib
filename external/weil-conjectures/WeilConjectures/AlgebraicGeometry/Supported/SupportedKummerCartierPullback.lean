/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.PicardTensorDualComparisonIso

/-!
# Cartier line bundle and canonical section under Cartier-preserving pullback

Source: Stacks Project, Tag 0C4U, lemma-pullback-effective-Cartier-divisors
(blueprint: lem-asd-supported-kummer-cartier-pullback).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible

variable {T T' : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
private theorem exists_pullback_ideal_iso (g : T' ⟶ T)
    {J : T.IdealSheafData} (hJ : J.IsInvertible) (hJ' : (J.comap g).IsInvertible) :
    ∃ e : (Modules.pullback g).obj J.toModules ≅ (J.comap g).toModules,
      e.hom ≫ (J.comap g).toModulesι = J.pullbackToModulesι g := by
  have := hJ.isInvertible_toModules
  have := Modules.IsInvertible.sheafOfModules_isInvertible ((Modules.pullback g).obj J.toModules)
  let φ : (Modules.pullback g).obj J.toModules ⟶ (J.comap g).toModules :=
    kernel.lift _ (J.pullbackToModulesι g) (J.pullbackToModulesι_comp_toPushforwardSubscheme g)
  have hφ : φ ≫ (J.comap g).toModulesι = J.pullbackToModulesι g := kernel.lift_ι _ _ _
  have hi : IsIso φ := by
    refine Modules.isIso_of_isFreeGenerator φ fun y ↦ ?_
    obtain ⟨U, hyU, b, -, hU⟩ := hJ (g y)
    obtain ⟨s, hs⟩ := J.exists_toModulesι_app_eq (hU ▸ Ideal.mem_span_singleton_self b)
    obtain ⟨V, hyV, hVU, e, he⟩ :=
      Modules.exists_isFreeGenerator ((Modules.pullback g).obj J.toModules) (W := g ⁻¹ᵁ U.1) hyU
    obtain ⟨a, ha⟩ := he.exists_smul_eq (((Modules.pullback g).obj J.toModules).presheaf.map
      (homOfLE hVU).op (((Modules.pullbackPushforwardAdjunction g).unit.app J.toModules).app U.1 s))
    have hV : (J.comap g).ideal V =
        Ideal.span {T'.presheaf.map (homOfLE hVU).op (g.app U.1 b)} := by
      rw [J.ideal_comap_appLE g U V hVU, hU, Ideal.map_span, Set.image_singleton]
      rfl
    obtain ⟨a', ha'⟩ : ∃ a' : Γ(T', V.1), a' * T'.presheaf.map (homOfLE hVU).op (g.app U.1 b) =
        (J.comap g).toModulesι.app V.1 (φ.app V.1 e) :=
      Ideal.mem_span_singleton'.1 (by
        rw [← hV]
        exact ((J.comap g).range_toModulesι_app V).subset ⟨_, rfl⟩)
    have h1 := congrArg ((J.pullbackToModulesι g).app V.1) ha
    rw [Modules.Hom.app_smul, Modules.Hom.app_presheaf_map, pullbackToModulesι_app_unit, hs,
      ← hφ, Modules.Hom.comp_app] at h1
    rw [ConcreteCategory.comp_apply, ← ha'] at h1
    have haa' : a * a' = 1 := by
      have h2 : (a * a' - 1) * T'.presheaf.map (homOfLE hVU).op (g.app U.1 b) = 0 := by
        rw [sub_mul, one_mul, mul_assoc]
        exact sub_eq_zero.2 h1
      exact sub_eq_zero.1 (mem_nonZeroDivisors_iff_right.1 (hJ'.mem_nonZeroDivisors hV) _ h2)
    refine ⟨V.1, e, hyV, he, hJ'.isFreeGenerator _ fun V' h ↦ ?_⟩
    rw [← ha', map_mul, Ideal.span_singleton_mul_left_unit
      ((IsUnit.of_mul_eq_one a (mul_comm a a' ▸ haa')).map _), ← (J.comap g).map_ideal h, hV,
      Ideal.map_span, Set.image_singleton]
    rfl
  exact ⟨asIso φ, hφ⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_unit_comparison (h : T' ⟶ T) :
    (Modules.picardTensorComparison h).hom.app (Modules.unit T) ≫
      (Modules.pullbackObjUnitIso h).hom = Modules.tensorPullbackObjUnitToUnit h := by
  apply (Classical.choose (Modules.exists_tensorPullbackAdjunction h)).homEquiv _ _
    |>.injective
  rw [Adjunction.homEquiv_naturality_right]
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_apply]
  simp only [← Adjunction.homEquiv_apply, Modules.tensorPullbackObjUnitToUnit,
    Equiv.apply_symm_apply]
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    h.toRingCatSheafHom

set_option backward.isDefEq.respectTransparency false in
private theorem exists_tensor_ideal_iso (h : T' ⟶ T)
    {J : T.IdealSheafData} (hJ : J.IsInvertible) (hJ' : (J.comap h).IsInvertible) :
    ∃ e : (Modules.tensorPullback h).obj J.toModules ≅ (J.comap h).toModules,
      e.hom ≫ (J.comap h).toModulesι =
        (Modules.tensorPullback h).map J.toModulesι ≫
          Modules.tensorPullbackObjUnitToUnit h := by
  obtain ⟨e, he⟩ := exists_pullback_ideal_iso h hJ hJ'
  refine ⟨(Modules.picardTensorComparison h).app J.toModules ≪≫ e, ?_⟩
  simp only [Iso.trans_hom, Category.assoc, he, IdealSheafData.pullbackToModulesι]
  erw [← (Modules.picardTensorComparison h).hom.naturality_assoc]
  rw [tensor_unit_comparison]

end AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
