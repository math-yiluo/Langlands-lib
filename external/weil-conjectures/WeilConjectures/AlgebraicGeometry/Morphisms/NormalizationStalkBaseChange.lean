/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Relative normalization under stalk base change

The affine comparison proof adapts the smooth-base-change proof in
Mathlib.AlgebraicGeometry.Normalization, replacing smooth integral-closure base change
with TensorProduct.toIntegralClosure_bijective_of_isLocalization.

## References

* Stacks Project, Tag 0307 (localization of integral closure), Tag 035I, and Tag 02KH (flat base
  change of sections, degree zero)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
private theorem normalizationPullback_affine_localization {X C Y : Scheme.{u}}
    (f : X ⟶ C) (g : Y ⟶ C) [QuasiCompact f] [QuasiSeparated f] [Flat g]
    {U : C.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ g ⁻¹ᵁ U) (M : Submonoid Γ(C, U))
    (hM : letI := (g.appLE U V hVU).hom.toAlgebra; IsLocalization M Γ(Y, V)) :
    IsIso (f.normalizationPullback g ∣_ (pullback.snd f.fromNormalization g ⁻¹ᵁ V)) := by
  let W := pullback.snd f.fromNormalization g ⁻¹ᵁ V
  refine (isIso_morphismRestrict_iff_isIso_app _ (U := W) (hV.preimage _)).mpr ?_
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f.fromNormalization g) hVU le_rfl (UY := W)
    (by simp_rw [W, ← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV
    (hU.preimage f.fromNormalization).isCompact (hU.preimage f.fromNormalization).isQuasiSeparated
  rw [← @isIso_comp_left_iff _ _ _ _ _ _ _ this,
    ← isIso_comp_left_iff (pushout.congrHom f.fromNormalization.app_eq_appLE rfl).hom]
  algebraize [(f.app U).hom, (g.appLE U V hVU).hom, ((pullback.snd f g).app V).hom]
  have : IsLocalization M Γ(Y, V) := hM
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f g) hVU le_rfl (UY := pullback.snd f g ⁻¹ᵁ V)
    (by simp_rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV (f.isCompact_preimage hU.isCompact)
    (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  let e₀ := (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout ≪≫
    (pushout.congrHom f.app_eq_appLE rfl ≪≫ @asIso _ _ _ _ _ this :)
  let e : Γ(Y, V) ⊗[Γ(C, U)] Γ(X, f ⁻¹ᵁ U) ≃ₐ[Γ(Y, V)] Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    { toRingEquiv := e₀.commRingCatIsoToRingEquiv,
      commutes' r := by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e₀.hom) r =
          (pullback.snd f g).app V r
        congr 2
        simp [e₀, pushout.inr_desc_assoc, Scheme.Hom.app_eq_appLE] }
  let ψ : Γ(Y, V) ⊗[Γ(C, U)] integralClosure Γ(C, U) Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, V)]
      integralClosure Γ(Y, V) Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    e.mapIntegralClosure.toAlgHom.comp (TensorProduct.toIntegralClosure _ _ _)
  have hψ : Function.Bijective ψ := e.mapIntegralClosure.bijective.comp
    (TensorProduct.toIntegralClosure_bijective_of_isLocalization M)
  let φ : pushout (f.fromNormalization.app U) (g.appLE U V hVU) ⟶
      Γ((pullback.snd f g).normalization, f.normalizationPullback g ⁻¹ᵁ W) :=
    pushout.map _ _ (CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) Γ(X, f ⁻¹ᵁ U))))
      (g.appLE U V hVU) (f.normalizationObjIso hU).hom (𝟙 _) (𝟙 _)
      (by simp [Scheme.Hom.fromNormalization_app _ hU]) (by simp) ≫
    (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout.inv ≫
    (RingEquiv.ofBijective ψ.toRingHom hψ).toCommRingCatIso.hom ≫
    ((pullback.snd f g).normalizationObjIso hV).inv ≫
    (pullback.snd f g).normalization.presheaf.map (eqToHom
      (by simp only [W, ← Scheme.Hom.comp_preimage, Scheme.Hom.normalizationPullback_snd])).op
  convert! show IsIso φ by dsimp only [φ]; infer_instance using 1
  ext1
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_left, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE, eqToHom_op,
      Category.assoc, IsPushout.inl_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, IsIso.Iso.inv_inv,
      Category.assoc]
    have : Mono (CommRingCat.ofHom (integralClosure Γ(Y, V)
        Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V)).val.toRingHom) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    rw [← cancel_mono (CommRingCat.ofHom (Subalgebra.val _).toRingHom)]
    simp only [Category.assoc, Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.toNormalization_normalizationPullback_fst, ← CommRingCat.ofHom_comp]
    have H : pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ f ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
      exact Scheme.Hom.preimage_mono _ hVU
    trans (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom
        (integralClosure Γ(C, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom ≫ (pullback.fst f g).appLE _ _ H
    · rw [reassoc_of% Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE]
    · congr 1
      ext x
      change (pullback.fst f g).appLE _ _ H x = _
      trans (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e₀.hom) x
      · congr 2; simp [e₀, pushout.inl_desc_assoc]
      · simp [ψ, toIntegralClosure, e]; rfl
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_right, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.normalizationPullback_snd, eqToHom_op, IsPushout.inr_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, ← Scheme.Hom.app_eq_appLE,
      Scheme.Hom.fromNormalization_app _ hV, IsIso.Iso.inv_inv, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    exact congr(CommRingCat.ofHom $(ψ.comp_algebraMap.symm))

/-- Relative normalization commutes with base change from a base scheme to one of its stalks. -/
theorem Hom.isIso_normalizationPullback_stalk {S C P : Scheme.{u}}
    (c : C ⟶ S) (f : P ⟶ C) [QuasiCompact f] [QuasiSeparated f] (s : S) :
    IsIso (f.normalizationPullback (pullback.fst c (S.fromSpecStalk s))) := by
  let a := S.fromSpecStalk s
  let g := pullback.fst c a
  let d := pullback.snd c a
  let B := (S.affineCover.f (S.affineCover.idx s)).opensRange
  have hB : IsAffineOpen B := isAffineOpen_opensRange _
  have hsB : s ∈ B := S.affineCover.covers s
  have hBT : (⊤ : (Spec (S.presheaf.stalk s)).Opens) ≤ a ⁻¹ᵁ B := by
    intro z hz
    have hspec : a z ⤳ s := by
      exact ((IsLocalRing.specializes_closedPoint z).map a.continuous).trans
        (specializes_of_eq fromSpecStalk_closedPoint)
    exact hspec.mem_open B.isOpen hsB
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms _) fun x ↦ ?_
  have hxB : g ((pullback.snd f.fromNormalization g) x) ∈ c ⁻¹ᵁ B := by
    change c (g ((pullback.snd f.fromNormalization g) x)) ∈ B
    rw [← Hom.comp_apply, pullback.condition, Hom.comp_apply]
    exact hBT trivial
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUB⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open
    hxB (c ⁻¹ᵁ B).isOpen
  let V := g ⁻¹ᵁ U
  have hVP : V = g ⁻¹ᵁ U ⊓ d ⁻¹ᵁ ⊤ := by simp [V]
  have H : IsPullback g d c a := .of_hasPullback _ _
  have hsq := Hom.isPullback_resLE H hBT hUB hVP
  have : IsAffine (⊤ : (Spec (S.presheaf.stalk s)).Opens).toScheme :=
    isAffineOpen_top _
  have : IsAffine B.toScheme := hB
  have : IsAffine (Scheme.Opens.toScheme (X := C) U) := hU
  have hV : IsAffineOpen V := .of_isIso hsq.isoPullback.hom
  have hpush := (isIso_pushoutSection_iff H hBT hUB hVP).mp
    (isIso_pushoutSection_of_isAffineOpen H hBT hUB hVP hB
      (isAffineOpen_top _) hU)
  let α := c.appLE B U hUB
  let δ := a.appLE B ⊤ hBT
  let γ := g.appLE U V le_rfl
  let ε := d.appLE ⊤ V le_top
  let : Algebra Γ(S, B) Γ(C, U) := α.hom.toAlgebra
  let : Algebra Γ(S, B) Γ(Spec (S.presheaf.stalk s), ⊤) := δ.hom.toAlgebra
  let : Algebra Γ(C, U) Γ(pullback c a, V) := γ.hom.toAlgebra
  let : Algebra Γ(Spec (S.presheaf.stalk s), ⊤) Γ(pullback c a, V) := ε.hom.toAlgebra
  let : Algebra Γ(S, B) Γ(pullback c a, V) := (α ≫ γ).hom.toAlgebra
  have : IsScalarTower Γ(S, B) Γ(C, U) Γ(pullback c a, V) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S, B) Γ(Spec (S.presheaf.stalk s), ⊤)
      Γ(pullback c a, V) := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hpush.w)
  let M := (hB.primeIdealOf ⟨s, hsB⟩).asIdeal.primeCompl
  let : Algebra Γ(S, B) (S.presheaf.stalk s) :=
    (S.presheaf.germ B s hsB).hom.toAlgebra
  have : IsLocalization M (S.presheaf.stalk s) := hB.isLocalization_stalk ⟨s, hsB⟩
  have he : δ ≫ (ΓSpecIso (S.presheaf.stalk s)).hom = S.presheaf.germ B s hsB := by
    dsimp only [δ, a]
    rw [Hom.appLE, fromSpecStalk_app hsB]
    simp only [Category.assoc]
    have hm : (homOfLE (show a ⁻¹ᵁ B ≤ ⊤ from le_top)).op ≫ (homOfLE hBT).op =
        𝟙 (Opposite.op (⊤ : (Spec (S.presheaf.stalk s)).Opens)) := Subsingleton.elim _ _
    rw [← Functor.map_comp_assoc, hm, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id, Category.comp_id]
  let e : (S.presheaf.stalk s) ≃ₐ[Γ(S, B)] Γ(Spec (S.presheaf.stalk s), ⊤) :=
    { (ΓSpecIso (S.presheaf.stalk s)).symm.commRingCatIsoToRingEquiv with
      commutes' r := by
        exact congrArg (fun m : Γ(S, B) ⟶ Γ(Spec (S.presheaf.stalk s), ⊤) ↦ m r)
          ((Iso.comp_inv_eq (ΓSpecIso (S.presheaf.stalk s))).mpr he.symm) }
  have : IsLocalization M Γ(Spec (S.presheaf.stalk s), ⊤) :=
    IsLocalization.isLocalization_of_algEquiv M e
  have : Algebra.IsPushout Γ(S, B) Γ(C, U)
      Γ(Spec (S.presheaf.stalk s), ⊤) Γ(pullback c a, V) :=
    CommRingCat.isPushout_iff_isPushout.mp hpush
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid Γ(C, U) M)
      Γ(pullback c a, V) := (Algebra.isLocalization_iff_isPushout M
        Γ(Spec (S.presheaf.stalk s), ⊤)).mpr inferInstance
  refine ⟨pullback.snd f.fromNormalization g ⁻¹ᵁ V, hxU, ?_⟩
  exact normalizationPullback_affine_localization f g hU hV le_rfl
    (Algebra.algebraMapSubmonoid Γ(C, U) M) hloc

end AlgebraicGeometry.Scheme
