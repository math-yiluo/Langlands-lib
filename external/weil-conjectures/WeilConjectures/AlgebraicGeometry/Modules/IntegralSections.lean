/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.Rigidification
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-!
# Sections of invertible modules on an integral scheme

On an integral scheme `X`, a section of an invertible module which vanishes on a nonempty open
vanishes, and the tensor product of two nonzero sections of invertible modules is nonzero. If
moreover `Γ(X, 𝒪_X)` is a field, e.g. for `X` integral and proper over a field, an invertible
module `M` with a tensor inverse `N` is trivial as soon as both `M` and `N` have nonzero global
sections. This is the criterion behind the seesaw principle: the locus where an invertible module
is trivial on the fibres of a proper flat family is closed.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.eq_zero_of_presheaf_map_eq_zero`: a section of an invertible
  module on an integral scheme vanishing on a nonempty open vanishes.
- `AlgebraicGeometry.Scheme.Modules.tmulSection_ne_zero`: the tensor product of nonzero global
  sections of invertible modules on an integral scheme is nonzero.
- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_tensorObj_iso_unit`: the triviality
  criterion.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]

/-- **Sections of invertible modules on an integral scheme are determined on a nonempty open.**
A section `s` over `U` of an invertible module on an integral scheme whose restriction to a
nonempty open `W ⊆ U` vanishes, vanishes. -/
lemma eq_zero_of_presheaf_map_eq_zero (M : X.Modules) [M.IsInvertible] {U W : X.Opens}
    (h : W ≤ U) [Nonempty W] (s : Γ(M, U)) (hs : M.presheaf.map (homOfLE h).op s = 0) :
    s = 0 := by
  have := IsInvertible.sheafOfModules_isInvertible M
  let S : Sieve U := ⟨fun {V} _ ↦ ∃ (V' : X.Opens) (hV' : V ≤ V') (_ : V' ≤ U),
      (V' : Set X).Nonempty ∧ ∃ e : Γ(M, V'), IsFreeGenerator e,
    fun {V V''} _ ⟨V', hV', hV'U, hne, he⟩ g ↦ ⟨V', (leOfHom g).trans hV', hV'U, hne, he⟩⟩
  have hS : S ∈ Opens.grothendieckTopology X U := by
    intro x hx
    obtain ⟨V, hxV, hVU, e, he⟩ := exists_isFreeGenerator M hx
    exact ⟨V.1, homOfLE hVU, ⟨V.1, le_rfl, hVU, ⟨x, hxV⟩, e, he⟩, hxV⟩
  refine ((isSheaf_presheaf_comp_forget M) _ hS).isSeparatedFor.ext fun V i ⟨V', hV', hV'U, hne,
    e, he⟩ ↦ ?_
  change M.presheaf.map i.op s = M.presheaf.map i.op 0
  rw [map_zero, Subsingleton.elim i (homOfLE hV' ≫ homOfLE hV'U), ← presheaf_map_map_apply]
  suffices M.presheaf.map (homOfLE hV'U).op s = 0 by rw [this, map_zero]
  obtain ⟨a, ha⟩ := he.exists_smul_eq (M.presheaf.map (homOfLE hV'U).op s)
  have hVW : ((V' ⊓ W : X.Opens) : Set X).Nonempty :=
    by
      obtain ⟨⟨w, hw⟩⟩ := ‹Nonempty W›
      exact nonempty_preirreducible_inter V'.isOpen W.isOpen hne ⟨w, hw⟩
  have : Nonempty (V' ⊓ W : X.Opens) := hVW.to_subtype
  have h1 : X.presheaf.map (homOfLE (inf_le_left : V' ⊓ W ≤ V')).op a = 0 := by
    refine (he.map inf_le_left).smul_left_injective ?_
    change _ • _ = (0 : Γ(X, V' ⊓ W)) • _
    rw [zero_smul, ← map_smul, ha, presheaf_map_map_apply,
      Subsingleton.elim (homOfLE inf_le_left ≫ homOfLE hV'U)
        (homOfLE (inf_le_right : V' ⊓ W ≤ W) ≫ homOfLE h), ← presheaf_map_map_apply, hs, map_zero]
  rw [← ha, map_injective_of_isIntegral X (homOfLE (inf_le_left : V' ⊓ W ≤ V'))
    (h1.trans (map_zero _).symm), zero_smul]

/-- **Nonzero sections of invertible modules on an integral scheme have nonzero tensor
product.** If `s` and `t` are nonzero global sections of invertible modules on an
integral scheme, then `s ⊗ t ≠ 0`. -/
lemma tmulSection_ne_zero {M N : X.Modules} [M.IsInvertible] [N.IsInvertible] {s : Γ(M, ⊤)}
    {t : Γ(N, ⊤)} (hs : s ≠ 0) (ht : t ≠ 0) : tmulSection s t ≠ 0 := by
  have := IsInvertible.sheafOfModules_isInvertible M
  have := IsInvertible.sheafOfModules_isInvertible N
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨U₀, hxU₀, -, eM₀, hM₀⟩ := exists_isFreeGenerator M (TopologicalSpace.Opens.mem_top x)
  obtain ⟨U, hxU, hUU₀, eN, hN⟩ := exists_isFreeGenerator N hxU₀
  have hM := hM₀.map hUU₀
  set eM := M.presheaf.map (homOfLE hUU₀).op eM₀
  have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  obtain ⟨a, ha⟩ := hM.exists_smul_eq (M.presheaf.map (homOfLE le_top).op s)
  obtain ⟨b, hb⟩ := hN.exists_smul_eq (N.presheaf.map (homOfLE le_top).op t)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hs (eq_zero_of_presheaf_map_eq_zero M le_top s (by rw [← ha, zero_smul]))
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact ht (eq_zero_of_presheaf_map_eq_zero N le_top t (by rw [← hb, zero_smul]))
  intro hst
  have h := tmulSection_map (le_top : U.1 ≤ ⊤) s t
  rw [hst, map_zero, ← ha, ← hb, smul_tmulSection, tmulSection_smul, smul_smul] at h
  refine mul_ne_zero ha0 hb0 ((hM.tmulSection hN).smul_left_injective ?_)
  change _ • _ = (0 : Γ(X, U.1)) • _
  rw [← h, zero_smul]

/-- **A triviality criterion on an integral scheme with a field of global functions.** Let `X`
be integral with `Γ(X, 𝒪_X)` a field, e.g. integral and proper over a field. If invertible
modules `M`, `N` with `M ⊗ N ≅ 𝒪_X` both have nonzero global sections, then `M ≅ 𝒪_X`. -/
theorem nonempty_iso_unit_of_tensorObj_iso_unit (hX : IsField Γ(X, ⊤)) {M N : X.Modules}
    [M.IsInvertible] [N.IsInvertible] (e : M ⊗ N ≅ 𝟙_ X.Modules) {s : Γ(M, ⊤)}
    {t : Γ(N, ⊤)} (hs : s ≠ 0) (ht : t ≠ 0) : Nonempty (M ≅ 𝟙_ X.Modules) := by
  have := IsInvertible.sheafOfModules_isInvertible M
  have := IsInvertible.sheafOfModules_isInvertible N
  let := hX.toField
  -- `s ⊗ t` is a global free generator of `M ⊗ N`.
  set c : Γ(X, ⊤) := e.hom.app ⊤ (tmulSection s t) with hc
  have hc0 : c ≠ 0 := by
    intro h0
    refine tmulSection_ne_zero hs ht ?_
    calc tmulSection s t = (e.hom.app ⊤ ≫ e.inv.app ⊤) (tmulSection s t) := by
          rw [← Hom.comp_app, e.hom_inv_id, Hom.id_app, ConcreteCategory.id_apply]
      _ = e.inv.app ⊤ c := rfl
      _ = 0 := by rw [h0]; exact map_zero _
  have hgen : IsFreeGenerator (tmulSection s t) := by
    have h1 : IsFreeGenerator (M := 𝟙_ X.Modules) c := by
      have h := (isFreeGenerator_one (⊤ : X.Opens)).units_smul (Units.mk0 c hc0)
      have hc1 : ((Units.mk0 c hc0 : Γ(X, ⊤)) • (1 : Γ(X, ⊤)) : Γ(X, ⊤)) = c := mul_one c
      exact cast (congrArg _ hc1) h
    have h2 := h1.app_hom e.symm
    convert h2 using 1
    change _ = (e.hom.app ⊤ ≫ e.inv.app ⊤) _
    rw [← Hom.comp_app, e.hom_inv_id, Hom.id_app, ConcreteCategory.id_apply]
  -- Locally, the coefficient of `s` is a unit.
  have hloc (x : X) : ∃ U : X.Opens, x ∈ U ∧
      IsFreeGenerator (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s) := by
    obtain ⟨U₀, hxU₀, -, eM₀, hM₀⟩ :=
      exists_isFreeGenerator M (TopologicalSpace.Opens.mem_top x)
    obtain ⟨U, hxU, hUU₀, eN, hN⟩ := exists_isFreeGenerator N hxU₀
    have hM := hM₀.map hUU₀
    set eM := M.presheaf.map (homOfLE hUU₀).op eM₀
    obtain ⟨a, haeq⟩ := hM.exists_smul_eq (M.presheaf.map (homOfLE le_top).op s)
    obtain ⟨b, hb⟩ := hN.exists_smul_eq (N.presheaf.map (homOfLE le_top).op t)
    have h := tmulSection_map (le_top : U.1 ≤ ⊤) s t
    rw [← haeq, ← hb, smul_tmulSection, tmulSection_smul, smul_smul] at h
    obtain ⟨v, hv⟩ := (hM.tmulSection hN).exists_unit_smul_eq (hgen.map le_top)
    have hab : a * b = v := (hM.tmulSection hN).smul_left_injective (h.symm.trans hv)
    have ha : IsUnit a := isUnit_of_mul_isUnit_left (hab ▸ v.isUnit)
    refine ⟨U.1, hxU, ?_⟩
    rw [← haeq]
    exact hM.units_smul ha.unit
  choose U hxU hU using hloc
  have hs' : IsFreeGenerator s :=
    IsFreeGenerator.of_iSup s U (fun _ ↦ le_top)
      (fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩) hU
  have := isIso_homOfGlobalSection hs'
  exact ⟨(asIso (homOfGlobalSection M s)).symm⟩

end AlgebraicGeometry.Scheme.Modules
