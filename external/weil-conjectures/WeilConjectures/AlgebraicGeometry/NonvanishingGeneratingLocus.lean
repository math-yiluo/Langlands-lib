/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus

/-! # Nonvanishing and local generation of an invertible module

Source: Stacks Project, Modules, Lemma 01CY, proof at a stalk.
(blueprint: lem-sc-nonvanishing-iff-generates-at).
-/

@[expose] public section

universe u

open CategoryTheory TopCat.Presheaf

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem stalk_generator_bijective {X : Scheme.{u}} (M : X.Modules)
    {U : X.Opens} {e : Γ(M, U)} (he : IsFreeGenerator e) {x : X} (hx : x ∈ U) :
    Function.Bijective
      (fun r : X.presheaf.stalk x ↦
        r • TopCat.Presheaf.germ M.val.presheaf U x hx e) := by
  let f : X.presheaf.stalk x →ₗ[X.presheaf.stalk x] ↑(TopCat.Presheaf.stalk M.val.presheaf x) :=
    LinearMap.toSpanSingleton _ _ (TopCat.Presheaf.germ M.val.presheaf U x hx e)
  change Function.Bijective f
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro r hr
    obtain ⟨V, hVU, hxV, a, rfl⟩ := X.presheaf.exists_le_germ_eq r hx
    have hr' : TopCat.Presheaf.germ M.val.presheaf V x hxV
        (a • M.presheaf.map (homOfLE hVU).op e) =
        TopCat.Presheaf.germ M.val.presheaf V x hxV 0 := by
      erw [PresheafOfModules.germ_smul (R := X.presheaf) M.val,
        TopCat.Presheaf.germ_res_apply, map_zero]
      exact hr
    obtain ⟨W, hxW, i, j, hij⟩ := TopCat.Presheaf.germ_eq M.val.presheaf x hxV hxV _ _ hr'
    change M.presheaf.map i.op (a • M.presheaf.map (homOfLE hVU).op e) =
      M.presheaf.map j.op 0 at hij
    rw [map_smul, map_zero, Scheme.Modules.presheaf_map_map_apply] at hij
    have ha : X.presheaf.map i.op a = 0 := (he.map (i.le.trans hVU)).smul_left_injective
      (by
        dsimp only
        rw [zero_smul]
        exact hij)
    rw [← X.presheaf.germ_res_apply i x hxW a, ha, map_zero]
  · intro z
    obtain ⟨V, hVU, hxV, t, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq M.val.presheaf z hx
    obtain ⟨a, ha⟩ := (he.map hVU).exists_smul_eq t
    refine ⟨X.presheaf.germ V x hxV a, ?_⟩
    change X.presheaf.germ V x hxV a • TopCat.Presheaf.germ M.val.presheaf U x hx e = _
    erw [← TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE hVU) x hxV e,
      ← PresheafOfModules.germ_smul (R := X.presheaf) M.val, ha]

/-- A section of an invertible module has nonzero fibre value precisely where it is a
local free generator.

Source: Stacks Project, Modules, Lemma 01CY, proof at a stalk.
(blueprint: lem-sc-nonvanishing-iff-generates-at).

Proof: choose a free generator `e` on a neighbourhood of `x`, and write `s = a • e` there.
The induced stalk basis identifies the germ of `s` with the germ of `a` and identifies
`𝔪_x M_x` with `𝔪_x`. Thus nonvanishing means that the germ of `a` is a unit of the local
ring. This is equivalent to `x ∈ D(a)`. On `D(a)`, the coefficient is invertible, so `s`
is a free generator. Conversely, if `s` is a free generator near `x`, comparison of its
basis with `e` makes the germ of `a` a unit, so its class modulo `𝔪_x` is nonzero. -/
theorem mem_nonvanishingLocus_iff_generatesAt {X : Scheme.{u}} (M : X.Modules)
    [M.IsInvertible] (s : Γ(M, ⊤)) (x : X) :
    x ∈ nonvanishingLocus M s ↔ GeneratesAt s x := by
  have : SheafOfModules.IsInvertible.{u, u, u} M :=
    IsInvertible.sheafOfModules_isInvertible M
  obtain ⟨V, hxV, -, e, he⟩ := exists_isFreeGenerator M (x := x) (W := ⊤) trivial
  let a := he.coeff (M.presheaf.map (homOfLE le_top).op s)
  have hs : M.presheaf.map (homOfLE le_top).op s = a • e := (he.coeff_smul _).symm
  rw [generatesAt_iff_mem_basicOpen he hs hxV, X.mem_basicOpen _ _ hxV]
  let f : X.presheaf.stalk x →ₗ[X.presheaf.stalk x] ↑(TopCat.Presheaf.stalk M.val.presheaf x) :=
    LinearMap.toSpanSingleton _ _ (TopCat.Presheaf.germ M.val.presheaf V.1 x hxV e)
  have hf : Function.Bijective f := stalk_generator_bijective M he hxV
  have hmem (r : X.presheaf.stalk x) :
      f r ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x) (↑(TopCat.Presheaf.stalk M.val.presheaf x))) ↔
        r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    have h := congrArg (fun p : Submodule (X.presheaf.stalk x) (X.presheaf.stalk x) ↦ r ∈ p)
      (Submodule.comap_smul_top_of_surjective
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) f hf.2)
    simpa only [Submodule.mem_comap, LinearMap.ker_eq_bot.mpr hf.1, sup_bot_eq,
      Ideal.smul_eq_mul, Ideal.mul_top] using Iff.of_eq h
  change TopCat.Presheaf.germ M.val.presheaf ⊤ x trivial s ∉ _ ↔ _
  have hg : TopCat.Presheaf.germ M.val.presheaf ⊤ x trivial s =
      f (X.presheaf.germ V.1 x hxV a) := by
    erw [← TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE le_top) x hxV s,
      hs, PresheafOfModules.germ_smul (R := X.presheaf) M.val]
    rfl
  rw [hg, hmem, IsLocalRing.mem_maximalIdeal]
  exact not_not


end AlgebraicGeometry.Scheme.Modules
