/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.AlgebraicGeometry.Limits

/-! # Open base change of the direct image of the structure module

## References

* Stacks Project, Tags 008C and 0094, and the open-base-change calculation used in Tag 0EY6
* Tag 0EY6, base-change identification
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to an open chart commutes with the structure-module direct image. -/
theorem nonempty_open_base_change_structure_module_iso
    {Y L : Scheme.{u}} (j : Y ⟶ L) [IsOpenImmersion j]
    (U : L.Opens) {X : Scheme.{u}} (f : X ⟶ U.toScheme) :
    let g := f ≫ U.ι
    let B : L.CommAlgebraSheaf := Under.mk
      (⟨g.c⟩ : L.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj X.sheaf)
    let t := j ∣_ U
    let Z := CategoryTheory.Limits.pullback f t
    let p := pullback.snd f t ≫ (j ⁻¹ᵁ U).ι
    let C : Y.CommAlgebraSheaf := Under.mk
      (⟨p.c⟩ : Y.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} p.base).obj Z.sheaf)
    Nonempty (restrict B.toModule j ≅ C.toModule)  := by
  classical
  dsimp only
  let t := j ∣_ U
  let Z := CategoryTheory.Limits.pullback f t
  let i := pullback.fst f t
  let p := pullback.snd f t ≫ (j ⁻¹ᵁ U).ι
  let g := f ≫ U.ι
  have H : IsPullback i p g j :=
    (IsPullback.of_hasPullback f t).paste_vert (isPullback_morphismRestrict j U)
  have heq (T : Y.Opens) : i ''ᵁ (p ⁻¹ᵁ T) = g ⁻¹ᵁ (j ''ᵁ T) :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H.flip T
  refine ⟨(SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun T => ?_) ?_)⟩
  · let e : Γ(X, g ⁻¹ᵁ (j ''ᵁ T.unop)) ≅ Γ(Z, p ⁻¹ᵁ T.unop) :=
      X.presheaf.mapIso (eqToIso (heq T.unop)).op ≪≫ i.appIso (p ⁻¹ᵁ T.unop)
    refine ModuleCat.isoMk ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab).mapIso e) ?_
    intro (r : Γ(Y, T.unop))
    ext (m : Γ(X, g ⁻¹ᵁ (j ''ᵁ T.unop)))
    symm
    change e.hom (g.app (j ''ᵁ T.unop) ((j.appIso T.unop).inv r) * m) =
      p.app T.unop r * e.hom m
    rw [map_mul]
    congr 1
    have hs : g.app (j ''ᵁ T.unop) ≫ e.hom =
        (j.appIso T.unop).hom ≫ p.app T.unop := by
      dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.inv]
      rw [Hom.appIso_hom', Hom.map_appLE, Hom.app_eq_appLE g,
        Hom.appLE_comp_appLE, Hom.appIso_hom', Hom.app_eq_appLE p,
        Hom.appLE_comp_appLE]
      have hcongr : ∀ (a b : Z ⟶ L), a = b →
          ∀ ha hb, a.appLE (j ''ᵁ T.unop) (p ⁻¹ᵁ T.unop) ha =
            b.appLE (j ''ᵁ T.unop) (p ⁻¹ᵁ T.unop) hb := by
        rintro a b rfl ha hb
        rfl
      exact hcongr _ _ H.w _ _
    have hr := ConcreteCategory.congr_hom hs ((j.appIso T.unop).inv r)
    simpa only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] using hr
  · intro T S a
    ext (m : Γ(X, g ⁻¹ᵁ (j ''ᵁ T.unop)))
    change (i.appIso (p ⁻¹ᵁ S.unop)).hom
      (X.presheaf.map (eqToHom (heq S.unop)).op
        (X.presheaf.map ((TopologicalSpace.Opens.map g.base).map
          (j.opensFunctor.map a.unop)).op m)) =
        Z.presheaf.map ((TopologicalSpace.Opens.map p.base).map a.unop).op
          ((i.appIso (p ⁻¹ᵁ T.unop)).hom
            (X.presheaf.map (eqToHom (heq T.unop)).op m))
    have hn := Hom.appIso_hom_naturality i
      (((TopologicalSpace.Opens.map p.base).map a.unop).op)
    have hmaps : eqToHom (heq S.unop) ≫
        (TopologicalSpace.Opens.map g.base).map (j.opensFunctor.map a.unop) =
          i.opensFunctor.map ((TopologicalSpace.Opens.map p.base).map a.unop) ≫
            eqToHom (heq T.unop) :=
      Subsingleton.elim _ _
    have hmaps' : X.presheaf.map (eqToHom (heq T.unop)).op ≫
        X.presheaf.map (i.opensFunctor.map
          ((TopologicalSpace.Opens.map p.base).map a.unop)).op =
        X.presheaf.map ((TopologicalSpace.Opens.map g.base).map
          (j.opensFunctor.map a.unop)).op ≫
            X.presheaf.map (eqToHom (heq S.unop)).op := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, ← hmaps]
    have hn' := congrArg
      (fun k => X.presheaf.map (eqToHom (heq T.unop)).op ≫ k) hn
    simp only [Quiver.Hom.unop_op] at hn'
    erw [← Category.assoc, hmaps', Category.assoc] at hn'
    exact ConcreteCategory.congr_hom hn' m

end AlgebraicGeometry.Scheme.Modules
