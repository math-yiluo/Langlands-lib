/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionSemilinear

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
open Scheme.Modules
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

instance tensorResolutionAffineInclusionOpen (Y : Scheme.{u})
    (V U : Y.affineOpens) (h : V.1 ≤ U.1) :
    IsOpenImmersion (Spec.map (Y.presheaf.map (homOfLE h).op)) := by
  have : IsOpenImmersion (Spec.map (Y.presheaf.map (homOfLE h).op) ≫ U.2.fromSpec) := by
    rw [U.2.map_fromSpec V.2 (homOfLE h).op]
    infer_instance
  exact IsOpenImmersion.of_comp _ U.2.fromSpec

/-- The canonical identification of successive chart restrictions. -/
noncomputable def tensorResolutionChartRestrictionIso (Y : Scheme.{u})
    (V U : Y.affineOpens) (h : V.1 ≤ U.1) :
    restrictFunctor U.2.fromSpec ⋙
      restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op)) ≅
        restrictFunctor V.2.fromSpec :=
  (restrictFunctorComp _ _).symm ≪≫
    restrictFunctorCongr (U.2.map_fromSpec V.2 (homOfLE h).op)

/-- The chart restriction identification induces the original restriction of sections. -/
theorem tensorResolutionChartRestriction_sections (Y : Scheme.{u})
    (M : Y.Modules) (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (z : (moduleSpecΓFunctor (R := Γ(Y, U.1))).obj (M.restrict U.2.fromSpec)) :
    sectionsRestrictFromSpecLinearEquiv M V.2
      (((tensorResolutionChartRestrictionIso Y V U h).hom.app M).app ⊤
        (((restrictAdjunction (Spec.map (Y.presheaf.map (homOfLE h).op))).unit.app
          (M.restrict U.2.fromSpec)).app ⊤ z)) =
    M.val.map (homOfLE h).op (sectionsRestrictFromSpecLinearEquiv M U.2 z) := by
  simp only [tensorResolutionChartRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Hom.comp_app, ConcreteCategory.comp_apply,
    restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app,
    restrictAdjunction_unit_app_app,
    sectionsRestrictFromSpecLinearEquiv, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ z))) =
    M.presheaf.map _ (M.presheaf.map _ z)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 1

/-- The affine coefficient model has the chosen section coordinates. -/
theorem tensorResolutionChartModel_toOpen {Y : Scheme.{u}} (M : Y.Modules)
    [M.IsQuasicoherent] (U : Y.affineOpens)
    (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (s : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1)) (m : MA) :
    (tensorResolutionChartModel M U MA s).hom.app ⊤ (tilde.toOpen MA ⊤ m) =
      (sectionsRestrictFromSpecLinearEquiv M U.2).symm (s m) := by
  let e := s.trans (sectionsRestrictFromSpecLinearEquiv M U.2).symm
  change (M.restrict U.2.fromSpec).fromTildeΓ.app ⊤
    ((tilde.map e.toModuleIso.hom).app ⊤ (tilde.toOpen MA ⊤ m)) = e m
  have hm := congr($(tilde.toOpen_map_app e.toModuleIso.hom ⊤) m)
  change (tilde.map e.toModuleIso.hom).app ⊤ (tilde.toOpen MA ⊤ m) =
    tilde.toOpen (moduleSpecΓFunctor.obj (M.restrict U.2.fromSpec)) ⊤ (e m) at hm
  rw [hm]
  exact fromTildeΓ_app_toOpen _ _

/-- A semilinear map with the chosen section formula induces the canonical
restriction of the coefficient sheaf. -/
theorem tensorResolutionChartModel_naturality {Y : Scheme.{u}} (M : Y.Modules)
    [M.IsQuasicoherent] (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (MB : ModuleCat.{u} (Γ(Y, V.1) : Type u))
    (sA : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sB : MB ≃ₗ[Γ(Y, V.1)] M.val.obj (op V.1))
    (a : MA ⟶ (ModuleCat.restrictScalars
      (Y.presheaf.map (homOfLE h).op).hom).obj MB)
    (ha : ∀ x, sB (a x) = M.val.map (homOfLE h).op (sA x)) :
    (restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))).map
        (tensorResolutionChartModel M U MA sA).hom ≫
        (tensorResolutionChartRestrictionIso Y V U h).hom.app M =
      tensorResolutionSemilinearMap (Y.presheaf.map (homOfLE h).op) a ≫
        (tensorResolutionChartModel M V MB sB).hom := by
  let φ := Y.presheaf.map (homOfLE h).op
  let eA := tensorResolutionChartModel M U MA sA
  let eB := tensorResolutionChartModel M V MB sB
  apply ((tensorResolutionSemilinearAdjunction φ).homEquiv MA
    (M.restrict V.2.fromSpec)).injective
  apply ModuleCat.hom_ext
  ext m
  change ((tensorResolutionChartRestrictionIso Y V U h).hom.app M).app ⊤
      (((restrictFunctor (Spec.map φ)).map eA.hom).app ⊤
        (((restrictAdjunction (Spec.map φ)).unit.app (tilde MA)).app ⊤
          (tilde.toOpen MA ⊤ m))) =
    eB.hom.app ⊤ ((tensorResolutionSemilinearMap φ a).app ⊤
      (((restrictAdjunction (Spec.map φ)).unit.app (tilde MA)).app ⊤
        (tilde.toOpen MA ⊤ m)))
  have hu := congrArg (fun f ↦ f.app ⊤ (tilde.toOpen MA ⊤ m))
    ((restrictAdjunction (Spec.map φ)).unit.naturality eA.hom)
  change ((restrictAdjunction (Spec.map φ)).unit.app (M.restrict U.2.fromSpec)).app ⊤
      (eA.hom.app ⊤ (tilde.toOpen MA ⊤ m)) =
    (((restrictFunctor (Spec.map φ)).map eA.hom).app ⊤
      (((restrictAdjunction (Spec.map φ)).unit.app (tilde MA)).app ⊤
        (tilde.toOpen MA ⊤ m))) at hu
  rw [← hu, tensorResolutionSemilinearMap_unit]
  apply (sectionsRestrictFromSpecLinearEquiv M V.2).injective
  rw [tensorResolutionChartRestriction_sections]
  dsimp only [eA, eB]
  rw [tensorResolutionChartModel_toOpen, tensorResolutionChartModel_toOpen,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact (ha m).symm

end AlgebraicGeometry
