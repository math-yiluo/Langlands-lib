/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSectionFactorization
import WeilConjectures.AlgebraicGeometry.Modules.HomSection

/-! # Free coordinates under a factorization of scheme maps

## References

* Stacks Project, Tag 01CA, functoriality and associativity of tensor products
* Stacks Project, Tag 01CA, tensor associativity and functoriality
-/

@[expose] public section

noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unit_pullbackΓ {X Y : Scheme.{u}} (f : Y ⟶ X) (a : Γ(X, ⊤)) :
    (pullbackObjUnitIso f).hom.app ⊤ (pullbackΓ f (unit X) a) = f.appTop a := by
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at h
  have h' : (pullbackPushforwardAdjunction f).unit.app (unit X) ≫
      (pushforward f).map (pullbackObjUnitIso f).hom =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := h
  have ht := congrArg (fun (q : unit X ⟶ (pushforward f).obj (unit Y)) ↦ Hom.app q ⊤ a) h'
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply] at ht
  rw [pullbackΓ_apply]
  exact ht

private theorem unit_comp {X Y Z : Scheme.{u}}
    (g : Y ⟶ X) (h : Z ⟶ X) (v : Z ⟶ Y) (hv : v ≫ g = h) :
    (pullbackCompOfEq v g h hv (unit X)).hom ≫ (pullbackObjUnitIso h).hom =
      (pullback v).map (pullbackObjUnitIso g).hom ≫ (pullbackObjUnitIso v).hom := by
  let e := (pullback v).mapIso (pullbackObjUnitIso g) ≪≫ pullbackObjUnitIso v
  let t := pullbackΓ v _ (pullbackΓ g (unit X) (1 : Γ(X, ⊤)))
  have he : e.hom.app ⊤ t = (1 : Γ(Z, ⊤)) := by
    change (pullbackObjUnitIso v).hom.app ⊤
      (((pullback v).map (pullbackObjUnitIso g).hom).app ⊤ t) = _
    dsimp only [t]
    rw [pullbackΓ_naturality, unit_pullbackΓ g, unit_pullbackΓ v]
    rw [map_one g.appTop.hom, map_one v.appTop.hom]
  have hi : e.inv.app ⊤ (1 : Γ(Z, ⊤)) = t := by
    rw [← he]
    change (e.hom ≫ e.inv).app ⊤ t = t
    rw [e.hom_inv_id]
    rfl
  rw [← cancel_epi e.inv]
  apply unit_hom_ext
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, hi]
  dsimp only [t]
  rw [pullbackCompOfEq_hom_app_pullbackΓ, unit_pullbackΓ, map_one]
  exact he.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Pulling a section through a factorization commutes with any map into finite free. -/
theorem pullback_free_coordinates_naturality
    {X Y Z : Scheme.{u}} (g : Y ⟶ X) (h : Z ⟶ X) (v : Z ⟶ Y)
    (hv : v ≫ g = h) (M : X.Modules) (r : ℕ)
    (α : M ⟶ free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))
    (x : Γ((pullback g).obj M, ⊤)) (i : Fin r) :
    freeSectionsEquiv (ULift.{u} (Fin r))
      (((pullback h).map α ≫ (pullbackFreeIso h (ULift.{u} (Fin r))).hom).app ⊤
        (pullbackSectionFactorization g h v hv M x)) (ULift.up i) =
      v.appTop (freeSectionsEquiv (ULift.{u} (Fin r))
        (((pullback g).map α ≫ (pullbackFreeIso g (ULift.{u} (Fin r))).hom).app ⊤ x)
          (ULift.up i)) := by
  let I := ULift.{u} (Fin r)
  let β : M ⟶ unit X := α ≫ freeπ (ULift.up i)
  have hn : (pullbackCompOfEq v g h hv M).hom ≫ (pullback h).map β =
      (pullback v).map ((pullback g).map β) ≫
        (pullbackCompOfEq v g h hv (unit X)).hom := by
    subst h
    simpa [pullbackCompOfEq, pullbackCongr] using
      ((pullbackComp v g).hom.naturality β).symm
  have hc : (pullbackCompOfEq v g h hv M).hom ≫ (pullback h).map α ≫
      (pullbackFreeIso h I).hom ≫ freeπ (ULift.up i) =
      (pullback v).map ((pullback g).map α ≫ (pullbackFreeIso g I).hom ≫
        freeπ (ULift.up i)) ≫ (pullbackObjUnitIso v).hom := by
    rw [pullbackFreeIso_hom_freeπ, pullbackFreeIso_hom_freeπ]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    change (pullbackCompOfEq v g h hv M).hom ≫ (pullback h).map β ≫
      (pullbackObjUnitIso h).hom = _
    rw [← Category.assoc, hn, Category.assoc, unit_comp]
    simp only [β, Functor.map_comp, Category.assoc]
  change Hom.app (freeπ (X := Z) (ULift.up i)) ⊤
    (((pullback h).map α ≫ (pullbackFreeIso h I).hom).app ⊤
      (pullbackSectionFactorization g h v hv M x)) = _
  unfold pullbackSectionFactorization
  change ((pullbackCompOfEq v g h hv M).hom ≫ (pullback h).map α ≫
    (pullbackFreeIso h I).hom ≫ freeπ (ULift.up i)).app ⊤ (pullbackΓ v _ x) = _
  rw [hc]
  change (pullbackObjUnitIso v).hom.app ⊤
    (((pullback v).map ((pullback g).map α ≫ (pullbackFreeIso g I).hom ≫
      freeπ (ULift.up i))).app ⊤ (pullbackΓ v _ x)) = _
  rw [pullbackΓ_naturality, unit_pullbackΓ]
  rfl

end AlgebraicGeometry.Scheme.Modules
