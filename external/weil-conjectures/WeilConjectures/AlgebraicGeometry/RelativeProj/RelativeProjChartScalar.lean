/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic

/-! # Coefficients in the structural map of a relative Proj chart

## References

* Stacks Project, Constructions, Tags 01ME and 01NQ
* Stacks, Tags 01ME and 01NQ, affine structural maps in relative Proj
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.GradedAlgebraData

attribute [local irreducible] Scheme.GradedAlgebraData.relProj
  Scheme.GradedAlgebraData.relProjHom Scheme.GradedAlgebraData.relProjι

private theorem localization_map_constant (B : Type u) [CommRing B]
    (M N : Submonoid B) (h : M ≤ N.comap (RingHom.id B)) (a : B) :
    IsLocalization.map (Localization N) (RingHom.id B) h
      (Localization.mk a 1 : Localization M) = Localization.mk a 1 := by
  simpa only [Localization.mk_one_eq_algebraMap, RingHom.id_apply] using
    (IsLocalization.map_eq (M := M) (S := Localization M) (Q := Localization N)
      (g := RingHom.id B) h a)

/-- The structural map reads a base coefficient as its constant homogeneous fraction.
This is a ring-section identity; it asserts no existence or descent of module sheaves. -/
theorem chart_scalar_value {S : Scheme.{u}} (A : S.GradedAlgebraData)
    (U : S.affineOpens) (r : Γ(S, U.1))
    (x : A.relProjι U ⁻¹ᵁ (A.relProjHom ⁻¹ᵁ U.1)) :
    (((A.relProjι U).app (A.relProjHom ⁻¹ᵁ U.1)
      (A.relProjHom.app U.1 r)).1 x).val =
        Localization.mk (algebraMap Γ(S, U.1) (A.obj U) r) 1 := by
  have topInv_app (X : Scheme.{u}) :
      X.topIso.inv.appTop = (⊤ : X.Opens).topIso.hom := by
    apply (cancel_epi (⊤ : X.Opens).topIso.inv).mp
    change X.topIso.hom.appTop ≫ X.topIso.inv.appTop = _
    rw [← Scheme.Hom.comp_appTop, X.topIso.inv_hom_id]
    simp only [Scheme.Hom.id_appTop, Iso.inv_hom_id]
  let P := Proj (A.grading U)
  let W : P.Opens := A.relProjι U ⁻¹ᵁ (A.relProjHom ⁻¹ᵁ U.1)
  let g := Proj.toSpecOfAlgebra (A.grading U)
  have he : A.relProjι U ≫ A.relProjHom = g ≫ U.2.fromSpec := by
    rw [A.relProjι_relProjHom, A.toOpen_eq, Category.assoc]
    rfl
  have hr : (A.relProjι U).app (A.relProjHom ⁻¹ᵁ U.1)
      (A.relProjHom.app U.1 r) =
      ((Scheme.ΓSpecIso Γ(S, U.1)).inv ≫ g.appLE ⊤ W (by simp)) r := by
    change (A.relProjι U ≫ A.relProjHom).appLE U.1 W le_rfl r = _
    have hcongr (f f' : P ⟶ S) (e : f = f')
        (hf : W ≤ f ⁻¹ᵁ U.1) (hf' : W ≤ f' ⁻¹ᵁ U.1) :
        f.appLE U.1 W hf = f'.appLE U.1 W hf' := by
      subst e
      rfl
    rw [hcongr _ _ he le_rfl (by rw [← he]; exact le_rfl),
      Scheme.Hom.comp_appLE, U.2.fromSpec_app_of_le U.1 le_rfl]
    simp only [homOfLE_refl, op_id]
    rw [S.presheaf.map_id]
    simp only [Category.id_comp, Category.assoc]
    exact congrArg (fun k ↦ ((Scheme.ΓSpecIso Γ(S, U.1)).inv ≫ k) r)
      (g.map_appLE _ _)
  rw [hr]
  change ((((Scheme.ΓSpecIso Γ(S, U.1)).inv ≫ g.appTop ≫
    P.presheaf.map (homOfLE le_top).op) r).1 x).val = _
  simp only [g, Proj.toSpecOfAlgebra, Scheme.Hom.comp_appTop, Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  simp only [Proj.toSpecZero, Scheme.Hom.comp_appTop, Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  have hb : (Proj.basicOpenToSpec (A.grading U) 1).appTop =
      (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection (A.grading U) 1 ≫
        (Proj.basicOpen (A.grading U) 1).topIso.inv :=
    Proj.basicOpenToSpec_app_top (A.grading U) 1
  rw [hb]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [topInv_app]
  simp only [Scheme.isoOfEq_inv, Scheme.homOfLE_appTop,
    Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv]
  change (((Proj.awayToSection (A.grading U) 1)
    (HomogeneousLocalization.fromZeroRingHom (A.grading U) (Submonoid.powers 1)
      (algebraMap Γ(S, U.1) (A.grading U 0) r))).1 ⟨x.1, by simp⟩).val = _
  exact (ProjectiveSpectrum.Proj.awayToSection_apply (A.grading U) 1
    (HomogeneousLocalization.fromZeroRingHom (A.grading U) (Submonoid.powers 1)
      (algebraMap Γ(S, U.1) (A.grading U 0) r)) ⟨x.1, by simp⟩).trans (by
    change IsLocalization.map (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl)
      (RingHom.id (A.obj U)) _
        (Localization.mk (algebraMap Γ(S, U.1) (A.obj U) r) 1) =
          Localization.mk (algebraMap Γ(S, U.1) (A.obj U) r) 1
    exact localization_map_constant _ _ _ _ _)

end AlgebraicGeometry.Scheme.GradedAlgebraData
