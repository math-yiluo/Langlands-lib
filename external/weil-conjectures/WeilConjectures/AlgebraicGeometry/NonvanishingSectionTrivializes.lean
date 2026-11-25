/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # A nonvanishing section trivializes an invertible module

Source: literature/stacks-project/modules.tex, Lemma (Tag 01CY).
(blueprint: lem-weil-pbc-nonvanishing-section-trivializes)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- A local free generator stays a basis on stalks, by representing germs on smaller opens. -/
private theorem stalk_generator_bijective {Y : Scheme.{u}} {L : Y.Modules}
    {U : Y.Opens} {e : Γ(L, U)} (he : IsFreeGenerator e) (x : Y) (hx : x ∈ U) :
    Function.Bijective (fun a : Y.presheaf.stalk x ↦
      a • L.presheaf.germ U x hx e) := by
  constructor
  · intro a b hab
    obtain ⟨V, hVU, hxV, r, hr⟩ := Y.presheaf.exists_le_germ_eq a hx
    obtain ⟨W, hWU, hxW, t, ht⟩ := Y.presheaf.exists_le_germ_eq b hx
    have hge (Z : Y.Opens) (hZU : Z ≤ U) (hxZ : x ∈ Z) (c : Γ(Y, Z)) :
        L.presheaf.germ Z x hxZ (c • L.presheaf.map (homOfLE hZU).op e) =
          Y.presheaf.germ Z x hxZ c • L.presheaf.germ U x hx e := by
      rw [germ_smul L, L.presheaf.germ_res_apply]
    have hab' := hab
    dsimp only at hab'
    rw [← hr, ← ht, ← hge V hVU hxV r, ← hge W hWU hxW t] at hab'
    obtain ⟨Z, hxZ, iV, iW, hZ⟩ := L.presheaf.germ_eq x hxV hxW _ _ hab'
    rw [map_smul, map_smul, presheaf_map_map_apply, presheaf_map_map_apply] at hZ
    have hrt := ((he.map ((leOfHom iV).trans hVU)).smul_left_injective hZ)
    have hg := congrArg (Y.presheaf.germ Z x hxZ) hrt
    rw [Y.presheaf.germ_res_apply, Y.presheaf.germ_res_apply, hr, ht] at hg
    exact hg
  · intro m
    obtain ⟨V, hVU, hxV, t, ht⟩ := L.presheaf.exists_le_germ_eq m hx
    obtain ⟨a, ha⟩ := (he V hVU).2 t
    refine ⟨Y.presheaf.germ V x hxV a, ?_⟩
    rw [← ht, ← ha, germ_smul L, L.presheaf.germ_res_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The stalk definition of nonvanishing agrees with the open off the zero scheme. -/
private theorem nonvanishing_eq_compl_support (Y : Scheme.{u}) (L : Y.Modules)
    [L.IsInvertible] (s : Γ(L, ⊤)) :
    nonvanishingLocus L s = ((Hom.zeroLocus (homOfGlobalSection L s)).support.compl : Set Y) := by
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    IsInvertible.sheafOfModules_isInvertible L
  ext x
  obtain ⟨V, hxV, -, e, he⟩ := exists_isFreeGenerator L (x := x) (W := ⊤) trivial
  let c := he.coeff ((homOfGlobalSection L s).app V.1 (unitSectionsEquiv _ 1))
  have hs : L.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op s = c • e := by
    rw [← homOfGlobalSection_app_one]
    exact (he.coeff_smul _).symm
  let ex := L.presheaf.germ V.1 x hxV e
  have hb : Function.Bijective (fun a : Y.presheaf.stalk x ↦ a • ex) :=
    stalk_generator_bijective he x hxV
  have hspan : Submodule.span (Y.presheaf.stalk x) {ex} = ⊤ :=
    (Submodule.span_singleton_eq_top_iff (Y.presheaf.stalk x) ex).2 hb.2
  have hmem (a : Y.presheaf.stalk x) :
      a • ex ∈ (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) •
        (⊤ : Submodule (Y.presheaf.stalk x) (L.presheaf.stalk x)) ↔
      a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x) := by
    rw [← hspan, Submodule.mem_smul_span_singleton]
    exact ⟨fun ⟨b, hbI, hba⟩ ↦ hb.1 hba ▸ hbI, fun ha ↦ ⟨a, ha, rfl⟩⟩
  have hgs : L.presheaf.germ ⊤ x trivial s = Y.presheaf.germ V.1 x hxV c • ex := by
    rw [← L.presheaf.germ_res_apply (homOfLE le_top) x hxV s, hs, germ_smul L]
  have hD := basicOpen_coeff_eq (homOfGlobalSection L s) V he
  have hxD : x ∈ Y.basicOpen c ↔
      x ∈ (Hom.zeroLocus (homOfGlobalSection L s)).support.compl := by
    change x ∈ Y.basicOpen
      (he.coeff ((homOfGlobalSection L s).app V.1 (unitSectionsEquiv _ 1))) ↔ _
    rw [show Y.basicOpen c = V.1 ⊓
      (Hom.zeroLocus (homOfGlobalSection L s)).support.compl from hD]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hxV, h⟩⟩
  change L.presheaf.germ ⊤ x trivial s ∉
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) •
      (⊤ : Submodule (Y.presheaf.stalk x) (L.presheaf.stalk x)) ↔ _
  rw [hgs, hmem, IsLocalRing.mem_maximalIdeal]
  change _ ↔ x ∈ (Hom.zeroLocus (homOfGlobalSection L s)).support.compl
  rw [← hxD, Y.mem_basicOpen c x hxV]
  simp

/-- A global section `s` of an invertible module `L` trivializes it on its non-vanishing
locus `Y_s = nonvanishingLocus L s` (germ of `s` outside `𝔪_y L_y`): `Y_s` is the underlying
set of an open `U`, the restriction to `U` (`SheafOfModules.overFunctor`) of the map
`homOfGlobalSection L s : 𝒪_Y ⟶ L`, `a ↦ a • s|`, is an isomorphism
`𝒪_Y|_U ≅ L|_U`, and consequently every section `t` of `L` over an open `V ⊆ U` is
`a • s|_V` for a unique `a ∈ 𝒪_Y(V)` (written `t / s`).

Proof (Stacks, Lemma 01CY): openness and the isomorphism are local, so trivialize `L` on an
open `W`, `L|_W ≅ 𝒪_W` with `s ↦ f`; there `Y_s ∩ W` is the basic open `D(f)`, hence
open, and these opens glue to `U`. At `y ∈ U` the stalk `L_y` is free of rank one and
`s_y ∉ 𝔪_y L_y`, so by Nakayama `s_y` is a basis of `L_y` and the stalk map `a ↦ a s_y` is
bijective; a morphism of sheaves of modules on `U` bijective on all stalks is an
isomorphism. Applying the inverse isomorphism to `t ∈ L(V)`, `V ⊆ U`, gives the unique `a`
(equivalently, the inverse section `s'` of `L^{⊗-1}` over `U` with `s'(s|_U) = 1` gives
`a = s'(t)`).
(blueprint: lem-weil-pbc-nonvanishing-section-trivializes)
-/
theorem nonvanishing_section_trivializes (Y : Scheme.{u}) (L : Y.Modules)
    [L.IsInvertible] (s : Γ(L, ⊤)) :
    ∃ U : Y.Opens, (U : Set Y) = nonvanishingLocus L s ∧
      IsIso ((SheafOfModules.overFunctor Y.ringCatSheaf U).map (homOfGlobalSection L s)) ∧
      ∀ (V : Y.Opens), V ≤ U → ∀ (t : Γ(L, V)),
        ∃! a : Γ(Y, V), t = a • L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s := by
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    IsInvertible.sheafOfModules_isInvertible L
  let U := (Hom.zeroLocus (homOfGlobalSection L s)).support.compl
  have hgen := isFreeGenerator_app_one_of_le (homOfGlobalSection L s) (U := U) le_rfl
  have hb (V : Y.Opens) (hV : V ≤ U) :
      Function.Bijective (fun a : Γ(Y, V) ↦
        a • L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s) := by
    have h := hgen V hV
    change Function.Bijective (fun r : Γ(Y, V) ↦
      r • L.presheaf.map (homOfLE hV).op
        ((homOfGlobalSection L s).app U (1 : Γ(Y, U)))) at h
    rw [homOfGlobalSection_app_one] at h
    rw [presheaf_map_map_apply] at h
    convert h using 1
  refine ⟨U, (nonvanishing_eq_compl_support Y L s).symm, ?_, ?_⟩
  · let F := SheafOfModules.forget (Y.ringCatSheaf.over U) ⋙
      PresheafOfModules.toPresheaf (Y.ringCatSheaf.over U).obj
    rw [← isIso_iff_of_reflects_iso _ F]
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (fun a : Γ(Y, V.unop.left) ↦
      (homOfGlobalSection L s).app V.unop.left a)
    simpa only [homOfGlobalSection_app] using hb V.unop.left (leOfHom V.unop.hom)
  · intro V hV t
    obtain ⟨a, ha⟩ := (hb V hV).2 t
    exact ⟨a, ha.symm, fun b hbt ↦ (hb V hV).1 (hbt.symm.trans ha.symm)⟩

end AlgebraicGeometry.Scheme.Modules
