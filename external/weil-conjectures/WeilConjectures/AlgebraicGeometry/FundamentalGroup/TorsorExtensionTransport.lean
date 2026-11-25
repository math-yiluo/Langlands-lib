/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorExtension
public import WeilConjectures.AlgebraicGeometry.Sites.GmTransport

/-!
# Restriction of the extension attached to a torsor along an étale monomorphism

Let `f : X ⟶ Y` be an étale monomorphism, for instance an isomorphism, `R` the restriction of
étale sheaves along `f` (`AlgebraicGeometry.Scheme.etaleRestriction`), `t'` a `ℤ/m`-torsor on
`Y` and `t` a `ℤ/m`-torsor on `X` with a morphism `h : P ⟶ P'` of total spaces over `f`
compatible with the actions, e.g. `t'` the transport of `t` along an isomorphism `f`. Pulling
back units along `h` maps `R (π'_* 𝔾ₘ)` to `π_* 𝔾ₘ` compatibly with the translations and with
the units of the base, hence maps the restriction of the extension
`0 ⟶ μ_m ⟶ K₂ ⟶ μ_m ⟶ 0` of `t'` to that of `t`. Consequently the cup products of `t` and `t'`
correspond under the restriction maps on cohomology
(`AlgebraicGeometry.Scheme.EtaleTorsor.restrictMu_cupMu`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleTorsor

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] {m : ℕ} [NeZero m]
  (t : EtaleTorsor (ULift.{u + 1} (ZMod m)) X) (t' : EtaleTorsor (ULift.{u + 1} (ZMod m)) Y)
  (h : t.P ⟶ t'.P) (hπ : t.π ≫ f = h ≫ t'.π)

/-- Pullback of units along `h : P ⟶ P'` over `f`: on an étale `U ⟶ X` it is the map
`Γ(U ×_Y P', 𝒪)ˣ ⟶ Γ(U ×_X P, 𝒪)ˣ` induced by `U ×_X P ⟶ U ×_Y P'`. -/
noncomputable def restrictW : (etaleRestriction f).obj t'.pushforwardGm ⟶ t.pushforwardGm :=
  ⟨{ app U := CommRingCat.unitsAddCommGrpULift.map
        (pullback.map U.unop.hom t.π ((etaleLocalization f).obj U.unop).hom t'.π (𝟙 _) h f
          (Category.id_comp _).symm hπ).appTop
     naturality {U V} φ := by
      change CommRingCat.unitsAddCommGrpULift.map _ ≫ CommRingCat.unitsAddCommGrpULift.map _ =
        CommRingCat.unitsAddCommGrpULift.map _ ≫ CommRingCat.unitsAddCommGrpULift.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      change ((MorphismProperty.Over.pullback @Etale ⊤ t'.π).map
          ((etaleLocalization f).map φ.unop)).left.appTop ≫ _ =
        _ ≫ ((MorphismProperty.Over.pullback @Etale ⊤ t.π).map φ.unop).left.appTop
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
        show ((MorphismProperty.Over.pullback @Etale ⊤ t'.π).map
            ((etaleLocalization f).map φ.unop)).left =
          pullback.map _ _ _ _ φ.unop.left (𝟙 _) (𝟙 _) (by simp) (by simp) from rfl,
        show ((MorphismProperty.Over.pullback @Etale ⊤ t.π).map φ.unop).left =
          pullback.map _ _ _ _ φ.unop.left (𝟙 _) (𝟙 _) (by simp) (by simp) from rfl]
      congr 1
      apply pullback.hom_ext <;> simp }⟩

lemma restrictW_translate (hv : t.vadd 1 ≫ h = h ≫ t'.vadd 1) :
    (etaleRestriction f).map (t'.pushforwardGmTranslate 1) ≫ t.restrictW f t' h hπ =
      t.restrictW f t' h hπ ≫ t.pushforwardGmTranslate 1 := by
  ext V : 3
  change CommRingCat.unitsAddCommGrpULift.map _ ≫ CommRingCat.unitsAddCommGrpULift.map _ =
    CommRingCat.unitsAddCommGrpULift.map _ ≫ CommRingCat.unitsAddCommGrpULift.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
  congr 1
  apply pullback.hom_ext <;> simp [hv]

@[reassoc (attr := simp)]
lemma restrictW_unit :
    (etaleRestriction f).map t'.pushforwardGmUnit ≫ t.restrictW f t' h hπ =
      t.pushforwardGmUnit := by
  ext V : 3
  change CommRingCat.unitsAddCommGrpULift.map _ ≫ CommRingCat.unitsAddCommGrpULift.map _ =
    CommRingCat.unitsAddCommGrpULift.map _
  rw [← Functor.map_comp]
  congr 1
  change (pullback.fst ((etaleLocalization f).obj V.unop).hom t'.π).appTop ≫
      (pullback.map V.unop.hom t.π ((etaleLocalization f).obj V.unop).hom t'.π (𝟙 _) h f
        (Category.id_comp _).symm hπ).appTop = (pullback.fst V.unop.hom t.π).appTop
  rw [← Scheme.Hom.comp_appTop, pullback.lift_fst, Category.comp_id]

variable (hv : t.vadd 1 ≫ h = h ≫ t'.vadd 1)

include hv in
@[reassoc]
lemma restrictW_gmDiff :
    (etaleRestriction f).map t'.gmDiff ≫ t.restrictW f t' h hπ =
      t.restrictW f t' h hπ ≫ t.gmDiff := by
  rw [gmDiff, gmDiff, Functor.map_sub, Preadditive.sub_comp, Preadditive.comp_sub,
    t.restrictW_translate f t' h hπ hv, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id]

/-- Pullback of units along `h` on `π_* μ_m`. -/
noncomputable def restrictV : (etaleRestriction f).obj t'.pushforwardMu ⟶ t.pushforwardMu :=
  kernel.lift _ ((etaleRestriction f).map (kernel.ι _) ≫ t.restrictW f t' h hπ) (by
    have e : m • 𝟙 ((etaleRestriction f).obj t'.pushforwardGm) =
        (etaleRestriction f).map (m • 𝟙 _) := by
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rw [Category.assoc, comp_nsmul_id, ← Category.assoc, e, ← Functor.map_comp, kernel.condition,
      Functor.map_zero, zero_comp])

@[reassoc (attr := simp)]
lemma restrictV_ι : t.restrictV f t' h hπ ≫ kernel.ι _ =
    (etaleRestriction f).map (kernel.ι _) ≫ t.restrictW f t' h hπ :=
  kernel.lift_ι _ _ _

include hv in
@[reassoc]
lemma restrictV_muDiff :
    (etaleRestriction f).map t'.muDiff ≫ t.restrictV f t' h hπ =
      t.restrictV f t' h hπ ≫ t.muDiff := by
  rw [← cancel_mono (kernel.ι (m • 𝟙 t.pushforwardGm)), Category.assoc, Category.assoc,
    muDiff_ι, restrictV_ι, restrictV_ι_assoc, ← Functor.map_comp_assoc, muDiff_ι,
    Functor.map_comp_assoc, t.restrictW_gmDiff f t' h hπ hv]

include hv in
/-- The map `R K₁' ⟶ K₁`. -/
noncomputable def restrictK₁ : (etaleRestriction f).obj (kernel t'.muDiff) ⟶ kernel t.muDiff :=
  kernel.lift _ ((etaleRestriction f).map (kernel.ι _) ≫ t.restrictV f t' h hπ) (by
    rw [Category.assoc, ← t.restrictV_muDiff f t' h hπ hv, ← Functor.map_comp_assoc,
      kernel.condition, Functor.map_zero, zero_comp])

@[reassoc (attr := simp)]
lemma restrictK₁_ι : t.restrictK₁ f t' h hπ hv ≫ kernel.ι _ =
    (etaleRestriction f).map (kernel.ι _) ≫ t.restrictV f t' h hπ :=
  kernel.lift_ι _ _ _

include hv in
/-- The map `R K₂' ⟶ K₂`. -/
noncomputable def restrictK₂ :
    (etaleRestriction f).obj (kernel (t'.muDiff ≫ t'.muDiff)) ⟶ kernel (t.muDiff ≫ t.muDiff) :=
  kernel.lift _ ((etaleRestriction f).map (kernel.ι _) ≫ t.restrictV f t' h hπ) (by
    rw [Category.assoc, ← t.restrictV_muDiff_assoc f t' h hπ hv,
      ← t.restrictV_muDiff f t' h hπ hv, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      Category.assoc, kernel.condition, Functor.map_zero, zero_comp])

@[reassoc (attr := simp)]
lemma restrictK₂_ι : t.restrictK₂ f t' h hπ hv ≫ kernel.ι _ =
    (etaleRestriction f).map (kernel.ι _) ≫ t.restrictV f t' h hπ :=
  kernel.lift_ι _ _ _

lemma restrictK₁_kernelToKernelComp :
    t.restrictK₁ f t' h hπ hv ≫ kernelToKernelComp t.muDiff =
      (etaleRestriction f).map (kernelToKernelComp t'.muDiff) ≫ t.restrictK₂ f t' h hπ hv := by
  rw [← cancel_mono (kernel.ι (t.muDiff ≫ t.muDiff)), Category.assoc, Category.assoc,
    kernelToKernelComp_ι, restrictK₁_ι, restrictK₂_ι, ← Functor.map_comp_assoc,
    kernelToKernelComp_ι]

lemma restrictK₂_kernelCompToKernel :
    t.restrictK₂ f t' h hπ hv ≫ kernelCompToKernel t.muDiff =
      (etaleRestriction f).map (kernelCompToKernel t'.muDiff) ≫ t.restrictK₁ f t' h hπ hv := by
  rw [← cancel_mono (kernel.ι t.muDiff), Category.assoc, Category.assoc, kernelCompToKernel_ι,
    restrictK₂_ι_assoc, restrictK₁_ι, ← Functor.map_comp_assoc, kernelCompToKernel_ι,
    Functor.map_comp_assoc, t.restrictV_muDiff f t' h hπ hv]

/-- The morphism from the restriction of the extension of `t'` to the extension of `t`. -/
noncomputable def restrictExtSeq : t'.extSeq.map (etaleRestriction f) ⟶ t.extSeq where
  τ₁ := t.restrictK₁ f t' h hπ hv
  τ₂ := t.restrictK₂ f t' h hπ hv
  τ₃ := t.restrictK₁ f t' h hπ hv
  comm₁₂ := t.restrictK₁_kernelToKernelComp f t' h hπ hv
  comm₂₃ := t.restrictK₂_kernelCompToKernel f t' h hπ hv

variable [Mono f]

lemma muUnit_restrictK₁ :
    (etaleRestriction f).map t'.muUnit ≫ t.restrictK₁ f t' h hπ hv =
      (rootsOfUnityRestrictionIso f m).hom ≫ t.muUnit := by
  rw [← cancel_mono (kernel.ι _), ← cancel_mono (kernel.ι (m • 𝟙 t.pushforwardGm))]
  simp only [Category.assoc, restrictK₁_ι, restrictV_ι, ← Functor.map_comp_assoc]
  simp [muUnit, muUnitV]

include hπ hv in
/-- **Cup products and restriction.** The cup products of `t` and `t'` correspond under the
restriction maps `H^q(Y, μ_m) ⟶ H^q(X, R μ_m) ≅ H^q(X, μ_m)`. -/
theorem restrictMu_cupMu (x : Sheaf.H (Y.rootsOfUnitySheaf m) 1) :
    Sheaf.H.map (rootsOfUnityRestrictionIso f m).hom 2 (etaleRestrictionH f _ 2 (t'.cupMu x)) =
      t.cupMu (Sheaf.H.map (rootsOfUnityRestrictionIso f m).hom 1
        (etaleRestrictionH f _ 1 x)) := by
  have := t.isIso_muUnit
  have := t'.isIso_muUnit
  have e₁ : (etaleRestriction f).map (inv t'.muUnit) ≫ (rootsOfUnityRestrictionIso f m).hom =
      t.restrictK₁ f t' h hπ hv ≫ inv t.muUnit := by
    rw [Functor.map_inv, IsIso.inv_comp_eq, ← Category.assoc, t.muUnit_restrictK₁ f t' h hπ hv,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  simp only [cupMu, AddMonoidHom.comp_apply]
  rw [etaleRestrictionH_map, ← Sheaf.H.map_comp_apply, e₁, Sheaf.H.map_comp_apply]
  congr 1
  refine (congrArg (Sheaf.H.map (t.restrictK₁ f t' h hπ hv) 2)
    (etaleRestrictionH_δSucc f t'.extSeq_shortExact 1 _)).trans ?_
  refine (Sheaf.H.map_δSucc _ t.extSeq_shortExact (t.restrictExtSeq f t' h hπ hv) 1 _).trans ?_
  congr 1
  change Sheaf.H.map (t.restrictK₁ f t' h hπ hv) 1 _ = _
  rw [etaleRestrictionH_map]
  exact (Sheaf.H.map_comp_apply ((etaleRestriction f).map t'.muUnit) _ _).symm.trans
    ((congrArg (fun φ ↦ Sheaf.H.map φ 1 _) (t.muUnit_restrictK₁ f t' h hπ hv)).trans
      (Sheaf.H.map_comp_apply _ _ _))

end AlgebraicGeometry.Scheme.EtaleTorsor
