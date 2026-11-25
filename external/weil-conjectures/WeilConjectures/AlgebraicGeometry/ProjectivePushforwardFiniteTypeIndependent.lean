/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.ProjectiveAffineFiniteCohomologyIndependent
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Independent finite type of projective pushforward

Source: Stacks Project, Tag 02O4, Lemma 30.16.3.
(blueprint: lem-pc-m1-projective-pushforward-finite-type-independent)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

-- Comparing restriction scalars expands the canonical open-subscheme isomorphisms.
set_option backward.isDefEq.respectTransparency false in
private theorem restrict_sections_smul {Y S : Scheme.{u}} (p : Y ⟶ S)
    (F : Y.Modules) (U : S.Opens) (r : Γ(U, ⊤))
    (x : Γ(F.restrict (p ⁻¹ᵁ U).ι, ⊤)) :
    F.presheaf.map (eqToHom (p ⁻¹ᵁ U).ι_image_top.symm).op
      (((F.restrict (p ⁻¹ᵁ U).ι).smul ((p ∣_ U).appTop r)).asHom.hom x) =
        p.app U (U.topIso.hom r) •
          F.presheaf.map (eqToHom (p ⁻¹ᵁ U).ι_image_top.symm).op x := by
  have hs := smul_restrictAppIso_hom_apply (p ⁻¹ᵁ U).ι F ⊤ ((p ∣_ U).appTop r) x
  refine (congrArg (fun z : Γ(F, (p ⁻¹ᵁ U).ι ''ᵁ ⊤) ↦
    F.presheaf.map (eqToHom (p ⁻¹ᵁ U).ι_image_top.symm).op z) hs).trans ?_
  rw [map_smul F]
  congr 1
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv,
    morphismRestrict_appTop, Scheme.Opens.topIso_hom,
    CommRingCat.comp_apply]
  simp only [← ConcreteCategory.comp_apply, Category.assoc]
  erw [Category.id_comp, ← Functor.map_comp]
  exact congr($((p.naturality (eqToHom U.ι_image_top.symm).op).symm) r)

set_option backward.isDefEq.respectTransparency false in
/-- Finite type of projective pushforward, obtained from degree-zero cohomology finiteness
without the general proper-coherence theorem.

Source: Stacks Project, Tag 02O4, Lemma 30.16.3, with Tags 01XZ and 01XJ.
(blueprint: lem-pc-m1-projective-pushforward-finite-type-independent)

Proof: restrict to an affine open V of S. Base change of the specified closed immersion
embeds its inverse image in projective space over V. The projective cohomology finiteness
argument (finite sums of twists and descending induction, Tag 01YS) in degree zero makes
Gamma(p^{-1}V,F) a finite Gamma(V,O)-module. Pushforward is quasi-coherent by the
localization theorem for quasi-compact separated morphisms (Tag 01XJ). Its restriction to
V is therefore associated to this finite module. The affine finite-type criterion,
applied on the covering of all affine opens of S, makes the pushforward finite type.
In Lean, degree-zero cohomology is identified linearly with sections, and the
open-subscheme section isomorphism transports finiteness to Gamma(p_*F,V). The scalar
calculation is naturality of p.app. This proof uses neither proper coherence nor its
higher-direct-image consequences. Empty coordinates give the zero module. -/
theorem isFiniteType_projective_pushforward_independent
    {Y S : Scheme.{u}} [IsLocallyNoetherian S]
    (p : Y ⟶ S) (N : Type u) [Finite N]
    (j : Y ⟶ ℙ(N; S)) [IsClosedImmersion j]
    (hj : j ≫ (ℙ(N; S) ↘ S) = p)
    (F : Y.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    ((pushforward p).obj F).IsFiniteType := by
  classical
  have : IsProper p := by rw [← hj]; infer_instance
  have hG : ((pushforward p).obj F).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated p F
  have hs (U : S.Opens) (hU : IsAffineOpen U) :
      Module.Finite Γ(S, U) Γ((pushforward p).obj F, U) := by
    have : IsAffine U.toScheme := hU
    have : IsLocallyNoetherian U.toScheme := inferInstance
    have : IsNoetherianRing Γ(U, ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.toScheme⟩
    let V := p ⁻¹ᵁ U
    let FV := F.restrict V.ι
    have hFV : FV.IsFinitePresentation := inferInstance
    have hFQ : FV.IsQuasicoherent := inferInstance
    have hw : (p ∣_ U) ≫ U.ι = (V.ι ≫ j) ≫ (ℙ(N; S) ↘ S) := by
      rw [morphismRestrict_ι, Category.assoc, hj]
    let k := ProjectiveSpace.liftBaseChange (p ∣_ U) (V.ι ≫ j) hw
    have hk : IsClosedImmersion k := by
      apply MorphismProperty.of_isPullback
        (ProjectiveSpace.isPullback_liftBaseChange (p ∣_ U)
          (show IsPullback V.ι (p ∣_ U) (j ≫ (ℙ(N; S) ↘ S)) U.ι from
            by rw [hj]; exact (isPullback_morphismRestrict p U).flip) hw)
      infer_instance
    have hkover := ProjectiveSpace.liftBaseChange_over (p ∣_ U) (V.ι ≫ j) hw
    let : Module Γ(U, ⊤) (FV.H 0) := Module.compHom _ (p ∣_ U).appTop.hom
    have hfinite : Module.Finite Γ(U, ⊤) (FV.H 0) := by
      change letI : Module Γ(U, ⊤) (FV.H 0) := Module.compHom _ (p ∣_ U).appTop.hom
        Module.Finite Γ(U, ⊤) (FV.H 0)
      rw [← hkover]
      exact finite_H_projective_affine_independent N k FV 0
    let : Module Γ(U, ⊤) Γ(FV, ⊤) := Module.compHom _ (p ∣_ U).appTop.hom
    let e : FV.H 0 ≃ₗ[Γ(U, ⊤)] Γ(FV, ⊤) :=
      { (H.zeroLinearEquiv FV).toAddEquiv with
        map_smul' := fun r x ↦ (H.zeroLinearEquiv FV).map_smul ((p ∣_ U).appTop r) x }
    have hsections : Module.Finite Γ(U, ⊤) Γ(FV, ⊤) :=
      Module.Finite.of_surjective e.toLinearMap e.surjective
    let c : Γ(FV, ⊤) →ₛₗ[U.topIso.hom.hom] Γ((pushforward p).obj F, U) :=
      { toFun := F.presheaf.map (eqToHom V.ι_image_top.symm).op
        map_add' := map_add _
        map_smul' := fun r x ↦ restrict_sections_smul p F U r x }
    exact Module.Finite.of_surjective c (by
      intro x
      refine ⟨F.presheaf.map (eqToHom V.ι_image_top).op x, ?_⟩
      change F.presheaf.map _ (F.presheaf.map _ x) = x
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      simp)
  exact ((((quasicoherent_finite_type_affine.{u, u} S).2 _ hG).2.1)
    S.affineOpens (fun U ↦ U.1) (iSup_affineOpens_eq_top S)
    (fun U ↦ U.2) (fun U ↦ hs U.1 U.2)).1

end AlgebraicGeometry.Scheme.Modules
