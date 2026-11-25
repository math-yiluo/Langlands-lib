/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Open restriction of the direct image under another open immersion

## References

* Stacks Project, Tag 008C (direct image on opens), and Tag 0094 (restriction to an open subspace)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The open-base-change comparison for an arbitrary module, without coherence hypotheses. -/
theorem nonempty_restrict_pushforward_open_iso
    {Y L : Scheme.{u}} (j : Y ⟶ L) [IsOpenImmersion j]
    (U : L.Opens) (P : U.toScheme.Modules) :
    Nonempty (restrict ((pushforward U.ι).obj P) j ≅
      (pushforward (j ⁻¹ᵁ U).ι).obj (restrict P (j ∣_ U)))  := by
  classical
  let W := j ⁻¹ᵁ U
  let t := j ∣_ U
  have heq (T : Y.Opens) : t ''ᵁ (W.ι ⁻¹ᵁ T) = U.ι ⁻¹ᵁ (j ''ᵁ T) :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      (isPullback_morphismRestrict j U).flip T
  refine ⟨(SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun T => ?_) ?_)⟩
  · refine ModuleCat.isoMk (P.presheaf.mapIso (eqToIso (heq T.unop)).op) ?_
    intro (r : Γ(Y, T.unop))
    ext (m : Γ(P, U.ι ⁻¹ᵁ (j ''ᵁ T.unop)))
    symm
    change P.presheaf.map (eqToHom (heq T.unop)).op
      (U.ι.app (j ''ᵁ T.unop) ((j.appIso T.unop).inv r) • m) =
      (t.appIso (W.ι ⁻¹ᵁ T.unop)).inv (W.ι.app T.unop r) •
        P.presheaf.map (eqToHom (heq T.unop)).op m
    erw [P.val.map_smul]
    congr 1
    apply (ConcreteCategory.bijective_of_isIso (t.appIso (W.ι ⁻¹ᵁ T.unop)).hom).1
    rw [Iso.inv_hom_id_apply]
    change (t.appIso (W.ι ⁻¹ᵁ T.unop)).hom
      ((U.toScheme.presheaf.map (eqToHom (heq T.unop)).op)
        (U.ι.app (j ''ᵁ T.unop) ((j.appIso T.unop).inv r))) = _
    have hs : U.ι.app (j ''ᵁ T.unop) ≫
        U.toScheme.presheaf.map (eqToHom (heq T.unop)).op ≫
          (t.appIso (W.ι ⁻¹ᵁ T.unop)).hom =
        j.appLE (j ''ᵁ T.unop) T.unop (j.preimage_image_eq T.unop).ge ≫
          W.ι.app T.unop := by
      rw [Hom.appIso_hom', Hom.map_appLE, Hom.app_eq_appLE U.ι,
        Hom.appLE_comp_appLE, Hom.app_eq_appLE W.ι, Hom.appLE_comp_appLE]
      have h := morphismRestrict_ι j U
      dsimp only [t, W]
      generalize_proofs h₁ h₂
      have hcongr : ∀ (a b : W.toScheme ⟶ L), a = b →
          ∀ ha hb, a.appLE (j ''ᵁ T.unop) (W.ι ⁻¹ᵁ T.unop) ha =
            b.appLE (j ''ᵁ T.unop) (W.ι ⁻¹ᵁ T.unop) hb := by
        rintro a b rfl ha hb
        rfl
      exact hcongr _ _ h _ _
    have hr := ConcreteCategory.congr_hom hs ((j.appIso T.unop).inv r)
    have hj : j.appLE (j ''ᵁ T.unop) T.unop (j.preimage_image_eq T.unop).ge =
        (j.appIso T.unop).hom := Hom.appIso_hom' j T.unop |>.symm
    rw [hj] at hr
    simpa only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] using hr
  · intro T S a
    ext (m : Γ(P, U.ι ⁻¹ᵁ (j ''ᵁ T.unop)))
    change P.presheaf.map _ (P.presheaf.map _ m) =
      P.presheaf.map _ (P.presheaf.map _ m)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 1


end AlgebraicGeometry.Scheme.Modules
