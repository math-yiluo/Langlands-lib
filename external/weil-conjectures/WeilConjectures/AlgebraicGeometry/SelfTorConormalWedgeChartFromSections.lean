/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.SelfTorAffineSection
public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafQuasicoherent
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso
import WeilConjectures.AlgebraicGeometry.Modules.AffineHom
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

private theorem affine_iso_from_sections {X : Scheme.{u}} [IsAffine X]
    (P Q : X.Modules) [P.IsQuasicoherent] [Q.IsQuasicoherent]
    (e : Γ(P, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(Q, ⊤)) :
    ∃ s : P ≅ Q, ∀ x : Γ(P, ⊤), s.hom.app ⊤ x = e x := by
  obtain ⟨f, hf⟩ := Scheme.Modules.exists_hom_app_top_eq_of_isAffine e.toLinearMap
  obtain ⟨g, hg⟩ := Scheme.Modules.exists_hom_app_top_eq_of_isAffine e.symm.toLinearMap
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply Scheme.Modules.hom_ext_of_isAffine
    intro x
    change g.app ⊤ (f.app ⊤ x) = x
    rw [hf, hg]
    exact e.symm_apply_apply x
  · apply Scheme.Modules.hom_ext_of_isAffine
    intro x
    change f.app ⊤ (g.app ⊤ x) = x
    rw [hg, hf]
    exact e.apply_symm_apply x

private theorem affine_over_iso_from_sections {X : Scheme.{u}}
    (P Q : X.Modules) (V : X.affineOpens)
    [(P.restrict V.1.ι).IsQuasicoherent] [(Q.restrict V.1.ι).IsQuasicoherent]
    (e : Γ(P, V.1) ≃ₗ[Γ(X, V.1)] Γ(Q, V.1)) :
    ∃ s : P.over V.1 ≅ Q.over V.1,
      ∀ x : Γ(P, V.1), s.hom.val.app (op (Over.mk (𝟙 V.1))) x = e x := by
  let U := V.1
  let χ₀ : Γ(P, U.ι ''ᵁ ⊤) ≃ₗ[Γ(X, U.ι ''ᵁ ⊤)] Γ(Q, U.ι ''ᵁ ⊤) :=
    U.ι_image_top.symm ▸ e
  let χ : Γ(P.restrict U.ι, ⊤) ≃ₗ[Γ(U.toScheme, ⊤)] Γ(Q.restrict U.ι, ⊤) :=
    { toFun := χ₀
      invFun := χ₀.symm
      left_inv := χ₀.left_inv
      right_inv := χ₀.right_inv
      map_add' := χ₀.map_add
      map_smul' := fun r x ↦ by
        change χ₀ ((U.ι.appIso ⊤).inv r • (show Γ(P, U.ι ''ᵁ ⊤) from x)) =
          (U.ι.appIso ⊤).inv r • χ₀ x
        exact χ₀.map_smul _ _ }
  have : IsAffine U.toScheme := V.2
  obtain ⟨t, ht⟩ := affine_iso_from_sections (P.restrict U.ι) (Q.restrict U.ι) χ
  let F := (Scheme.Modules.overEquiv U).functor
  let a := (Scheme.Modules.overFunctorEquiv U).app P
  let b := (Scheme.Modules.overFunctorEquiv U).app Q
  let s : P.over U ≅ Q.over U := F.preimageIso (a ≪≫ t ≪≫ b.symm)
  have hm (x : Γ(P, U.ι ''ᵁ ⊤)) :
      s.hom.val.app (op (Over.mk (homOfLE (U.ι_image_le ⊤)))) x = χ₀ x := by
    have hs := F.map_preimage (a ≪≫ t ≪≫ b.symm).hom
    have h := congr(Scheme.Modules.Hom.app $hs ⊤ x)
    change s.hom.val.app (op (Over.mk (homOfLE (U.ι_image_le ⊤)))) x =
      t.hom.app ⊤ x at h
    exact h.trans (ht x)
  refine ⟨s, ?_⟩
  have transport (W : X.Opens) (h : W = U) (hWU : W ≤ U)
      (g : Γ(P, W) ≃ₗ[Γ(X, W)] Γ(Q, W)) (hg : g = h.symm ▸ e)
      (hm : ∀ x : Γ(P, W), s.hom.val.app (op (Over.mk (homOfLE hWU))) x = g x) :
      ∀ x : Γ(P, U), s.hom.val.app (op (Over.mk (𝟙 U))) x = e x := by
    subst W
    subst g
    exact hm
  apply transport _ U.ι_image_top (U.ι_image_le ⊤) χ₀ _ hm
  rfl

private theorem affine_model_chart_quasicoherent {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    (U : Y.affineOpens) (M : ModuleCat.{u} (Γ(Y, U.1) : Type u)) :
    (((tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i).obj M).restrict
        (i ⁻¹ᵁ U.1).ι).IsQuasicoherent := by
  let V := i ⁻¹ᵁ U.1
  let a := i.resLE U.1 V le_rfl
  let B := ((tilde.functor Γ(Y, U.1)) ⋙
    Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj M
  let C := (Scheme.Modules.pushforward U.1.ι).obj B
  let t : Scheme.Modules.tensorPullback i ≅ Scheme.Modules.pullback i :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction i)
  let c : C.restrict U.1.ι ≅ B :=
    (Scheme.Modules.restrictFunctorAdjCounitIso U.1.ι).app B
  let r : ((Scheme.Modules.tensorPullback i).obj C).restrict V.ι ≅
      (Scheme.Modules.pullback a).obj B :=
    (Scheme.Modules.restrictFunctor V.ι).mapIso (t.app C) ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).app _ ≪≫
    (Scheme.Modules.pullbackComp V.ι i).app C ≪≫
    (Scheme.Modules.pullbackCongr (i.resLE_comp_ι le_rfl).symm).app C ≪≫
    ((Scheme.Modules.pullbackComp a U.1.ι).app C).symm ≪≫
    (Scheme.Modules.pullback a).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback U.1.ι).app C).symm ≪≫ c)
  have : B.IsQuasicoherent := by
    dsimp [B]
    infer_instance
  exact (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
    r.symm (by infer_instance)

/-- Sheafification of the affine conormal section calculation.
Source: Stacks Project, Tags 01R3 (conormal) and 01I6 (affine
quasi-coherent sheaves, full faithfulness, and exterior powers).
(blueprint: new-t2-self-tor-conormal-wedge-chart-from-sections).
Proof: Let V be the inverse-image chart. It is affine since i is a closed
immersion and U is affine. The ideal module is the kernel of the map from the
structure module to the direct image of the structure module of its closed
subscheme. Closed direct image and kernels preserve quasi-coherence, so this
ideal module is quasi-coherent. Identify tensorPullback with ordinary pullback
by uniqueness of left adjoints; pullback preserves quasi-coherence. Restrict
the conormal module to V and apply isQuasicoherent_exteriorSheaf_of_isAffine.
Use exteriorSheaf_restrict_iso to identify this exterior sheaf with E|V.
The restriction of T(M) to V is quasi-coherent:
on U the restricted pushforward is the associated A-module M, and its pullback
to the closed chart is the associated B-module B tensor_A M, where B = A/I.
Identify the over-site sheaves with module sheaves on the open subscheme V.
For quasi-coherent module sheaves on an affine scheme, a B-linear map on global
sections extends uniquely: on a principal open D(f) use its localization,
x/f^k mapping to e(x)/f^k, and glue over this basis. Apply this to both e and
e.symm. Their composites are identities on all principal opens, hence as sheaf
maps. Transport this isomorphism back to the over-site. Its component at the
terminal open is e by construction, proving the displayed equation for every
section. This step uses no pure-wedge equation and no choice of a section map.
For the empty chart both sheaves are zero and the same construction applies. -/
theorem exists_selfTor_conormal_wedge_chart_from_sections
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (n : ℕ) (U : Y.affineOpens)
    (e : let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
      let E := Scheme.Modules.exteriorPower N n
      let M := conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
      let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
        Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
      ((E.over (i ⁻¹ᵁ U.1)).val.obj
            (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1))))) ≃ₗ[Z.presheaf.obj (op (i ⁻¹ᵁ U.1))]
          ((T.obj M).over (i ⁻¹ᵁ U.1)).val.obj
            (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1))))) :
    let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let E := Scheme.Modules.exteriorPower N n
    let M := conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    ∃ s : E.over (i ⁻¹ᵁ U.1) ≅ (T.obj M).over (i ⁻¹ᵁ U.1),
      ∀ x : (E.over (i ⁻¹ᵁ U.1)).val.obj
        (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1)))),
        s.hom.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ U.1)))) x =
          e x := by
  let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
  let E := Scheme.Modules.exteriorPower N n
  let M := conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
  let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
    Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
  let V : Z.affineOpens := ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
  have : i.ker.toModules.IsQuasicoherent := by
    have := SheafOfModules.isQuasicoherent_unit (R := i.ker.subscheme.ringCatSheaf)
    have := SheafOfModules.isQuasicoherent_unit (R := Y.ringCatSheaf)
    have : SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf)
        ((SheafOfModules.pushforward i.ker.subschemeι.toRingCatSheafHom).obj
          (SheafOfModules.unit i.ker.subscheme.ringCatSheaf)) :=
      Scheme.Modules.isQuasicoherent_pushforward_of_isClosedImmersion i.ker.subschemeι _
    exact Scheme.Modules.isQuasicoherent_kernel i.ker.toPushforwardSubscheme
  let c : Scheme.Modules.tensorPullback i ≅ Scheme.Modules.pullback i :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction i)
  have : N.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
      (c.app i.ker.toModules).symm (by infer_instance)
  have : IsAffine V.1.toScheme := V.2
  obtain ⟨r⟩ := Scheme.Modules.exteriorSheaf_restrict_iso N n V.1
  have : (E.restrict V.1.ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent V.1.toScheme.ringCatSheaf).prop_of_iso r.symm
      (Scheme.Modules.isQuasicoherent_exteriorSheaf_of_isAffine (N.restrict V.1.ι) n)
  have : ((T.obj M).restrict V.1.ι).IsQuasicoherent :=
    affine_model_chart_quasicoherent i U M
  exact affine_over_iso_from_sections E (T.obj M) V e
end AlgebraicGeometry
