/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator

/-!
# Free generators of pullbacks

Let `g : X ⟶ Y` be a morphism of schemes and let `η : N ⟶ g_* g^* N` be the unit of the
adjunction `g^* ⊣ g_*`. We show that if `e` is a free generator of an `𝒪_Y`-module `N` on an open
`V`, then `η e` is a free generator of `g^* N` on `g ⁻¹ᵁ V`. For `V = ⊤` this follows from
`g^* 𝒪_Y ≅ 𝒪_X`; in general one restricts to `V` and compares the two ways around the square
formed by `g ∣_ V` and the open immersions `V.ι` and `(g ⁻¹ᵁ V).ι`.

We also show that a morphism of modules which is bijective on sections over all sufficiently small
opens is an isomorphism.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.homOfGlobalSection`: the morphism `𝒪_X ⟶ M`, `r ↦ r • u`,
  given by a global section `u` of `M` (via `SheafOfModules.unitHomEquiv`).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isIso_homOfGlobalSection`: a global free generator
  trivializes the module.

- `AlgebraicGeometry.Scheme.Modules.IsFreeGenerator.pullback_unit_app`: the unit of the adjunction
  `g^* ⊣ g_*` maps free generators to free generators.
- `AlgebraicGeometry.Scheme.Modules.isFreeGenerator_restrict_iff`: free generators of the
  restriction along an open immersion.
- `AlgebraicGeometry.Scheme.Modules.Hom.isIso_of_forall_bijective_app`: a morphism of modules
  which is locally bijective on sections is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The morphism `𝒪_X ⟶ M` corresponding to a global section `u` of `M`. -/
noncomputable def homOfGlobalSection (M : X.Modules) (u : Γ(M, ⊤)) :
    Modules.unit X ⟶ M :=
  (SheafOfModules.unitHomEquiv M).symm (_root_.PresheafOfModules.sectionsMk
    (fun W ↦ M.presheaf.map (homOfLE (le_top : W.unop ≤ ⊤)).op u)
    (fun _ _ f ↦ (presheaf_map_map_apply _ f.unop _).trans rfl))

/-- The morphism `𝒪_X ⟶ M` corresponding to a global section `u` sends `1` to `u`. -/
lemma homOfGlobalSection_app_one (M : X.Modules) (u : Γ(M, ⊤)) (U : X.Opens) :
    (homOfGlobalSection M u).app U (1 : Γ(X, U)) = M.presheaf.map (homOfLE le_top).op u :=
  congrArg (fun σ : M.sections ↦ σ.val (op U)) ((SheafOfModules.unitHomEquiv M).apply_symm_apply _)

/-- The morphism `𝒪_X ⟶ M` corresponding to a global section `u` sends `r` to `r • u`. -/
lemma homOfGlobalSection_app (M : X.Modules) (u : Γ(M, ⊤)) (U : X.Opens) (r : Γ(X, U)) :
    (homOfGlobalSection M u).app U r = r • M.presheaf.map (homOfLE le_top).op u := by
  rw [← homOfGlobalSection_app_one, ← Hom.app_smul]
  congr 1
  exact (mul_one r).symm

/-- A global free generator `u` of `M` trivializes `M`: `r ↦ r • u` is an isomorphism
`𝒪_X ≅ M`. -/
lemma isIso_homOfGlobalSection {M : X.Modules} {u : Γ(M, ⊤)} (hu : IsFreeGenerator u) :
    IsIso (homOfGlobalSection M u) := by
  rw [Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  have h : (fun r : Γ(X, U) ↦ (homOfGlobalSection M u).app U r) =
      fun r : Γ(X, U) ↦ r • M.presheaf.map (homOfLE le_top).op u :=
    funext (homOfGlobalSection_app M u U)
  have := hu U le_top
  rw [← h] at this
  exact this

/-- The unit of the adjunction `k^* ⊣ k_*` at `𝒪_Y` is `k^♯ : 𝒪_Y ⟶ k_* 𝒪_X`, up to
`k^* 𝒪_Y ≅ 𝒪_X`. -/
lemma pullbackPushforwardAdjunction_unit_app_unit (k : X ⟶ Y) :
    (pullbackPushforwardAdjunction k).unit.app (Modules.unit Y) =
      SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom ≫
        (pushforward k).map (pullbackObjUnitIso k).inv := by
  have h2 : (pullbackPushforwardAdjunction k).homEquiv _ _ (pullbackObjUnitIso k).hom =
      SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [← h2, Adjunction.homEquiv_unit, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

/-- The unit of the adjunction `k^* ⊣ k_*` maps a global free generator `s` of `L` to a free
generator of `k^* L`. -/
lemma IsFreeGenerator.pullback_unit_app_top (k : X ⟶ Y) {L : Y.Modules} {s : Γ(L, ⊤)}
    (hs : IsFreeGenerator s) :
    IsFreeGenerator (M := (pullback k).obj L) (U := k ⁻¹ᵁ ⊤)
      (((pullbackPushforwardAdjunction k).unit.app L).app ⊤ s) := by
  have := isIso_homOfGlobalSection hs
  let ψ : Modules.unit X ≅ (pullback k).obj L :=
    (pullbackObjUnitIso k).symm ≪≫ (pullback k).mapIso (asIso (homOfGlobalSection L s))
  have key : ((pullbackPushforwardAdjunction k).unit.app L).app ⊤ s =
      ψ.hom.app (k ⁻¹ᵁ ⊤) (1 : Γ(X, k ⁻¹ᵁ ⊤)) := by
    have h1 : s = (homOfGlobalSection L s).app ⊤ (1 : Γ(Y, ⊤)) := by
      rw [homOfGlobalSection_app_one, presheaf_map_id_apply]
    have h3 := (pullbackPushforwardAdjunction k).unit.naturality (homOfGlobalSection L s)
    have h4 := congrArg
      (fun φ : Modules.unit Y ⟶ (pushforward k).obj ((pullback k).obj L) ↦
        Hom.app φ ⊤ (1 : Γ(Y, ⊤))) h3
    simp only [Functor.id_map, Functor.comp_map, Hom.comp_app, ConcreteCategory.comp_apply,
      pullbackPushforwardAdjunction_unit_app_unit, pushforward_map_app] at h4
    rw [h1]
    refine h4.trans ?_
    have e1 : (Hom.app (SheafOfModules.unitToPushforwardObjUnit (Hom.toRingCatSheafHom k)) ⊤)
        (1 : Γ(Y, ⊤)) = (1 : Γ(X, k ⁻¹ᵁ ⊤)) :=
      map_one k.appTop.hom
    exact congrArg (fun x ↦ ((pullbackObjUnitIso k).inv ≫
      (pullback k).map (homOfGlobalSection L s)).app (k ⁻¹ᵁ ⊤) x) e1
  rw [key]
  exact (isFreeGenerator_one (k ⁻¹ᵁ ⊤)).app_hom ψ

/-- A section of the restriction of `M` along an open immersion `f` over `U` is a free generator
if and only if it is one as a section of `M` over `f ''ᵁ U`. -/
lemma isFreeGenerator_restrict_iff (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules)
    {U : X.Opens} (x : Γ(M, f ''ᵁ U)) :
    IsFreeGenerator (M := M.restrict f) (U := U) x ↔ IsFreeGenerator (M := M) (U := f ''ᵁ U) x := by
  have key (W : X.Opens) (h : W ≤ U) :
      (fun r : Γ(X, W) ↦ r • (M.restrict f).presheaf.map (homOfLE h).op x) =
        (fun r : Γ(Y, f ''ᵁ W) ↦ r • M.presheaf.map (homOfLE (f.image_mono h)).op x) ∘
          (f.appIso W).inv :=
    rfl
  refine ⟨fun hx W hW ↦ ?_, fun hx W hW ↦ ?_⟩
  · obtain ⟨W, rfl⟩ : ∃ W', f ''ᵁ W' = W :=
      ⟨f ⁻¹ᵁ W, by rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.mpr
        (hW.trans (f.image_le_opensRange U))]⟩
    have hW' : W ≤ U := (f.image_le_image_iff W U).mp hW
    have := (hx W hW').comp (ConcreteCategory.bijective_of_isIso (f.appIso W).hom)
    rw [key W hW', Function.comp_assoc] at this
    have e : (fun r : Γ(Y, f ''ᵁ W) ↦ r • M.presheaf.map (homOfLE (f.image_mono hW')).op x) ∘
        (f.appIso W).inv ∘ (f.appIso W).hom =
          fun r : Γ(Y, f ''ᵁ W) ↦ r • M.presheaf.map (homOfLE hW).op x := by
      funext r
      simp
    rw [e] at this
    exact this
  · rw [key W hW]
    exact (hx _ (f.image_mono hW)).comp (ConcreteCategory.bijective_of_isIso (f.appIso W).inv)

/-- A section whose restriction to an open with the same underlying set is a free generator is
a free generator. -/
lemma IsFreeGenerator.of_presheaf_map {M : X.Modules} {U V : X.Opens} (h : V ≤ U) (h' : U ≤ V)
    {e : Γ(M, U)} (he : IsFreeGenerator (M.presheaf.map (homOfLE h).op e)) :
    IsFreeGenerator e := by
  intro W hW
  have := he W (hW.trans h')
  simp only [presheaf_map_map_apply] at this
  exact this

/-- **The unit of the adjunction `g^* ⊣ g_*` maps free generators to free generators.** If `e` is
a free generator of `N` on `V`, then `η e` is a free generator of `g^* N` on `g ⁻¹ᵁ V`. -/
lemma IsFreeGenerator.pullback_unit_app (g : X ⟶ Y) {N : Y.Modules} {V : Y.Opens} {e : Γ(N, V)}
    (he : IsFreeGenerator e) :
    IsFreeGenerator (M := (pullback g).obj N) (U := g ⁻¹ᵁ V)
      (((pullbackPushforwardAdjunction g).unit.app N).app V e) := by
  let A1 := (pullbackPushforwardAdjunction g).comp (restrictAdjunction (g ⁻¹ᵁ V).ι)
  let A2 := (restrictAdjunction V.ι).comp (pullbackPushforwardAdjunction (g ∣_ V))
  let ρ : pushforward (g ⁻¹ᵁ V).ι ⋙ pushforward g ≅ pushforward (g ∣_ V) ⋙ pushforward V.ι :=
    pushforwardComp _ _ ≪≫ pushforwardCongr (morphismRestrict_ι g V).symm ≪≫
      (pushforwardComp _ _).symm
  have hu := unit_conjugateEquiv_symm A1 A2 ρ.hom N
  have hiso : IsIso ((conjugateEquiv A1 A2).symm ρ.hom) := inferInstance
  generalize (conjugateEquiv A1 A2).symm ρ.hom = Φ at hu hiso
  have h := congrArg (fun φ ↦ Hom.app φ V e) hu
  simp only [A1, A2, Adjunction.comp_unit_app, Hom.comp_app, ConcreteCategory.comp_apply, ρ,
    Iso.trans_hom, NatTrans.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app,
    Iso.symm_hom, pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app, Functor.comp_map] at h
  let e₁ : Γ(N.restrict V.ι, V.ι ⁻¹ᵁ V) :=
    N.presheaf.map (homOfLE (V.ι.image_preimage_le V)).op e
  have he₁ : IsFreeGenerator (M := N.restrict V.ι) e₁ :=
    (isFreeGenerator_restrict_iff _ _ _).2 (he.map _)
  have htop : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := V.ι_preimage_self.ge
  have h₂ := (he₁.map htop).pullback_unit_app_top (g ∣_ V)
  erw [Hom.app_presheaf_map ((pullbackPushforwardAdjunction (g ∣_ V)).unit.app (N.restrict V.ι))
    (homOfLE htop) e₁] at h₂
  have h₃ := IsFreeGenerator.of_presheaf_map (M := (pullback (g ∣_ V)).obj (N.restrict V.ι))
    (e := ((pullbackPushforwardAdjunction (g ∣_ V)).unit.app (N.restrict V.ι)).app _ e₁)
    (Scheme.Hom.preimage_mono _ htop) (by simp [V.ι_preimage_self]) h₂
  have h₄ := h₃.app_hom (asIso (Φ.app N))
  rw [asIso_hom] at h₄
  erw [← h] at h₄
  have t₁ : (g ⁻¹ᵁ V).ι ⁻¹ᵁ g ⁻¹ᵁ V = ⊤ := Scheme.Opens.ι_preimage_self _
  have t₂ : (g ∣_ V) ⁻¹ᵁ V.ι ⁻¹ᵁ V = ⊤ := by
    rw [Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
  have h₅ := IsFreeGenerator.of_presheaf_map (M := ((pullback g).obj N).restrict (g ⁻¹ᵁ V).ι)
    (U := (g ⁻¹ᵁ V).ι ⁻¹ᵁ g ⁻¹ᵁ V) (V := (g ∣_ V) ⁻¹ᵁ V.ι ⁻¹ᵁ V)
    (e := ((pullback g).obj N).presheaf.map (homOfLE ((g ⁻¹ᵁ V).ι.image_preimage_le _)).op
      (((pullbackPushforwardAdjunction g).unit.app N).app V e))
    (t₂.le.trans t₁.ge) (t₁.le.trans t₂.ge) h₄
  rw [isFreeGenerator_restrict_iff] at h₅
  refine IsFreeGenerator.of_presheaf_map _ ?_ h₅
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_idem]

/-- A morphism of modules which is bijective on sections over all sufficiently small opens is an
isomorphism. -/
lemma Hom.isIso_of_forall_bijective_app {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∀ W ≤ V, Function.Bijective (φ.app W)) :
    IsIso φ := by
  let f := (SheafOfModules.toSheaf X.ringCatSheaf).map φ
  have hinj : Sheaf.IsLocallyInjective f := ⟨fun {U} a b hab p hp ↦ by
    obtain ⟨V, hpV, hV⟩ := h p
    refine ⟨U.unop ⊓ V, homOfLE inf_le_left, (hV _ inf_le_right).1 ?_, hp, hpV⟩
    have := congrArg (N.presheaf.map (homOfLE (inf_le_left : U.unop ⊓ V ≤ U.unop)).op) hab
    exact (Hom.app_presheaf_map φ (homOfLE inf_le_left) a).trans
      (this.trans (Hom.app_presheaf_map φ (homOfLE inf_le_left) b).symm)⟩
  have hsurj : Sheaf.IsLocallySurjective f := ⟨fun {U} s p hp ↦ by
    obtain ⟨V, hpV, hV⟩ := h p
    obtain ⟨t, ht⟩ := (hV (U ⊓ V) inf_le_right).2
      (N.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s)
    exact ⟨U ⊓ V, homOfLE inf_le_left, ⟨t, ht⟩, hp, hpV⟩⟩
  have : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).1 ⟨hinj, hsurj⟩
  have : IsIso ((toPresheaf X).map φ) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map f))
  exact isIso_of_reflects_iso φ (toPresheaf X)

end AlgebraicGeometry.Scheme.Modules
