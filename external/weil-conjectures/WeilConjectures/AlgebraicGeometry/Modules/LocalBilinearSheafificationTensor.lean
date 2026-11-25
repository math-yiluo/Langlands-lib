/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension

/-!
# Extending a local bilinear presheaf pairing to sheaf tensors

## References

* Stacks Project, Tag 0GMW, and the open restriction adjunction
-/

@[expose] public section

universe v
open CategoryTheory Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_unit_bijective {X : Scheme.{v}} (M : X.Modules)
    (U W : X.Opens) (hW : W ≤ U) :
    Function.Bijective (((restrictAdjunction U.ι).unit.app M).val.app (op W)) := by
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hW]
  have hi : IsIso (M.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op) := by
    have hh : homOfLE (U.ι.image_preimage_le W) = (eqToIso he).hom :=
      Subsingleton.elim _ _
    rw [hh]
    infer_instance
  change Function.Bijective (((restrictAdjunction U.ι).unit.app M).app W)
  rw [restrictAdjunction_unit_app_app]
  exact ConcreteCategory.bijective_of_isIso _

private theorem local_bilinear_tensor_morphism {X : Scheme.{v}}
    (F G : _root_.PresheafOfModules.{v} X.ringCatSheaf.obj) (K : X.Modules)
    (β : ∀ W : X.Opensᵒᵖ,
      F.obj W →ₗ[X.presheaf.obj W] G.obj W →ₗ[X.presheaf.obj W] K.val.obj W)
    (hβ : ∀ {W Z : X.Opensᵒᵖ} (g : W ⟶ Z) (x : F.obj W) (y : G.obj W),
      β Z (F.map g x) (G.map g y) = K.val.map g (β W x y)) :
    let S : _root_.PresheafOfModules.{v} X.ringCatSheaf.obj ⥤ X.Modules :=
      PresheafOfModules.sheafification.{v} (𝟙 X.ringCatSheaf.obj)
    let η := (PresheafOfModules.sheafificationAdjunction.{v} (𝟙 X.ringCatSheaf.obj)).unit
    ∃ φ : S.obj F ⊗ S.obj G ⟶ K,
      ∀ (W : X.Opensᵒᵖ) (x : F.obj W) (y : G.obj W),
        φ.val.app W (tmulSection ((η.app F).app W x) ((η.app G).app W y)) = β W x y := by
  dsimp only
  let : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (𝟙 X.ringCatSheaf.obj) :=
    Presheaf.isLocallyInjective_of_injective _ _ (fun _ ↦ Function.injective_id)
  let : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (𝟙 X.ringCatSheaf.obj) :=
    Presheaf.isLocallySurjective_of_surjective _ _ (fun _ ↦ Function.surjective_id)
  obtain ⟨γ, ⟨hγ, hγunit⟩, _⟩ :=
    PresheafOfModules.existsUnique_bilinear_sheafification_extension
      X.presheaf X.sheaf (𝟙 X.ringCatSheaf.obj) F G K β hβ
  obtain ⟨φ, hφ, _⟩ := SheafOfModules.tensor_bilinear_universal X.sheaf
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj F)
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj G) K γ hγ
  exact ⟨φ, fun W x y ↦ (hφ W _ _).trans (hγunit W x y)⟩

private theorem restrictPushforward_bilinear_pairing {X : Scheme.{v}}
    (F G : _root_.PresheafOfModules.{v} X.ringCatSheaf.obj) (H : X.Modules)
    (U : X.Opens)
    (b : ∀ W : X.Opens, W ≤ U →
      F.obj (op W) →ₗ[X.presheaf.obj (op W)]
        G.obj (op W) →ₗ[X.presheaf.obj (op W)] H.val.obj (op W))
    (hb : ∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) x y,
      b Z (hZW.trans hW) (F.map (homOfLE hZW).op x) (G.map (homOfLE hZW).op y) =
        H.val.map (homOfLE hZW).op (b W hW x y)) :
    ∃ β : ∀ W : X.Opensᵒᵖ,
        F.obj W →ₗ[X.presheaf.obj W] G.obj W →ₗ[X.presheaf.obj W]
          ((pushforward U.ι).obj (H.restrict U.ι)).val.obj W,
      (∀ {W Z : X.Opensᵒᵖ} (g : W ⟶ Z) (x : F.obj W) (y : G.obj W),
        β Z (F.map g x) (G.map g y) =
          ((pushforward U.ι).obj (H.restrict U.ι)).val.map g (β W x y)) ∧
      (∀ (W : X.Opens) (hW : W ≤ U) (x : F.obj (op W)) (y : G.obj (op W)),
        β (op W) x y =
          ((restrictAdjunction U.ι).unit.app H).val.app (op W) (b W hW x y)) := by
  let j := U.ι
  let K := (pushforward j).obj (H.restrict j)
  let V (W : X.Opens) := j ''ᵁ (j ⁻¹ᵁ W)
  have hV (W : X.Opens) : V W ≤ U := U.ι_image_le _
  let k (W : X.Opens) := (homOfLE (j.image_preimage_le W)).op
  let β : ∀ W : X.Opensᵒᵖ,
      F.obj W →ₗ[X.presheaf.obj W] G.obj W →ₗ[X.presheaf.obj W] K.val.obj W :=
    fun W ↦ LinearMap.mk₂ (X.presheaf.obj W) (M := F.obj W)
      (Nₗ := G.obj W) (Pₗ := K.val.obj W)
      (fun x y ↦ b (V W.unop) (hV W.unop) (F.map (k W.unop) x) (G.map (k W.unop) y))
      (by intros; simp only [map_add, LinearMap.add_apply])
      (by
        intro c x y
        rw [PresheafOfModules.map_smul, (b _ _).map_smul, LinearMap.smul_apply]
        change X.presheaf.map (k W.unop) c •
          (b (V W.unop) (hV W.unop) (F.map (k W.unop) x) (G.map (k W.unop) y)) =
          (j.appIso (j ⁻¹ᵁ W.unop)).inv (j.app W.unop c) •
          (b (V W.unop) (hV W.unop) (F.map (k W.unop) x) (G.map (k W.unop) y))
        rw [← CommRingCat.comp_apply, j.app_appIso_inv]
        rfl)
      (by intros; rw [map_add, map_add])
      (by
        intro c x y
        rw [PresheafOfModules.map_smul, (b _ _ _).map_smul]
        change X.presheaf.map (k W.unop) c •
          (b (V W.unop) (hV W.unop) (F.map (k W.unop) x) (G.map (k W.unop) y)) =
          (j.appIso (j ⁻¹ᵁ W.unop)).inv (j.app W.unop c) •
          (b (V W.unop) (hV W.unop) (F.map (k W.unop) x) (G.map (k W.unop) y))
        rw [← CommRingCat.comp_apply, j.app_appIso_inv]
        rfl)
  have hβ : ∀ {W Z : X.Opensᵒᵖ} (g : W ⟶ Z) (x : F.obj W) (y : G.obj W),
      β Z (F.map g x) (G.map g y) = K.val.map g (β W x y) := by
    intro W Z g x y
    let hZW := leOfHom g.unop
    have hVZW : V Z.unop ≤ V W.unop :=
      j.image_mono ((TopologicalSpace.Opens.map j.base).monotone hZW)
    let l := (homOfLE hVZW).op
    have hf : F.map (k Z.unop) (F.map g x) =
        F.map l (F.map (k W.unop) x) := by
      rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
      rfl
    have hg : G.map (k Z.unop) (G.map g y) =
        G.map l (G.map (k W.unop) y) := by
      rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
      rfl
    change b (V Z.unop) _ (F.map (k Z.unop) (F.map g x))
      (G.map (k Z.unop) (G.map g y)) =
        H.val.map l (b (V W.unop) _ (F.map (k W.unop) x) (G.map (k W.unop) y))
    rw [hf, hg]
    exact hb _ _ _ hVZW _ _
  refine ⟨β, hβ, ?_⟩
  intro W hW x y
  exact hb W (V W) hW (j.image_preimage_le W) x y

set_option backward.isDefEq.respectTransparency false in
/-- Local bilinear presheaf pairings into a sheaf extend through sheafification and tensor. -/
theorem local_bilinear_sheafification_tensor_extension {X : Scheme.{v}}
    (F G : _root_.PresheafOfModules.{v} X.ringCatSheaf.obj) (H : X.Modules)
    (U : X.Opens)
    (b : ∀ W : X.Opens, W ≤ U →
      F.obj (op W) →ₗ[X.presheaf.obj (op W)]
        G.obj (op W) →ₗ[X.presheaf.obj (op W)] H.val.obj (op W))
    (hb : ∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) x y,
      b Z (hZW.trans hW) (F.map (homOfLE hZW).op x) (G.map (homOfLE hZW).op y) =
        H.val.map (homOfLE hZW).op (b W hW x y)) :
    let S : _root_.PresheafOfModules.{v} X.ringCatSheaf.obj ⥤ X.Modules :=
      PresheafOfModules.sheafification.{v} (𝟙 X.ringCatSheaf.obj)
    let η := (PresheafOfModules.sheafificationAdjunction.{v} (𝟙 X.ringCatSheaf.obj)).unit
    ∃ d : ∀ W : X.Opens, W ≤ U →
      (S.obj F ⊗ S.obj G).val.obj (op W) →ₗ[X.presheaf.obj (op W)] H.val.obj (op W),
      (∀ W hW x y,
        d W hW (tmulSection ((η.app F).app (op W) x) ((η.app G).app (op W) y)) =
          b W hW x y) ∧
      (∀ (W Z : X.Opens) (hW : W ≤ U) (hZW : Z ≤ W) y,
        H.val.map (homOfLE hZW).op (d W hW y) =
          d Z (hZW.trans hW) ((S.obj F ⊗ S.obj G).val.map (homOfLE hZW).op y)) := by
  classical
  dsimp only
  let j := U.ι
  let K := (pushforward j).obj (H.restrict j)
  let q : H ⟶ K := (restrictAdjunction j).unit.app H
  obtain ⟨β, hβ, hβunit⟩ := restrictPushforward_bilinear_pairing F G H U b hb
  obtain ⟨φ, hφ⟩ := local_bilinear_tensor_morphism F G K β hβ
  let e (W : X.Opens) (hW : W ≤ U) :=
    LinearEquiv.ofBijective (q.val.app (op W)).hom (restrict_unit_bijective H U W hW)
  let d (W : X.Opens) (hW : W ≤ U) := (e W hW).symm.toLinearMap.comp
    (φ.val.app (op W)).hom
  refine ⟨d, ?_, ?_⟩
  · intro W hW x y
    apply (e W hW).injective
    change e W hW ((e W hW).symm (φ.val.app (op W) (tmulSection _ _))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact (hφ (op W) x y).trans (hβunit W hW x y)
  · intro W Z hW hZW y
    apply (e Z (hZW.trans hW)).injective
    have hq := PresheafOfModules.naturality_apply q.val (homOfLE hZW).op (d W hW y)
    change q.val.app (op Z) (H.val.map (homOfLE hZW).op (d W hW y)) =
      e Z (hZW.trans hW) ((e Z (hZW.trans hW)).symm
        (φ.val.app (op Z) (_)))
    rw [LinearEquiv.apply_symm_apply, hq]
    change K.val.map (homOfLE hZW).op
      (e W hW ((e W hW).symm (φ.val.app (op W) y))) = _
    rw [LinearEquiv.apply_symm_apply]
    exact (PresheafOfModules.naturality_apply φ.val (homOfLE hZW).op y).symm

end AlgebraicGeometry.Scheme.Modules
