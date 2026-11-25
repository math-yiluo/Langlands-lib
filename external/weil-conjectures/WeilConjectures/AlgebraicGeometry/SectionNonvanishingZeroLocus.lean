/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators

/-! # The two conventions for a section's nonvanishing locus

Source: Stacks Project, Properties, Section 01PR and Lemma 01PW;
Modules, Lemma 01CY.
(blueprint: lem-weil-pbc-section-nonvanishing-zero-locus).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem bijective_smul_germ {X : Scheme.{u}} (M : X.Modules)
    {V : X.Opens} {e : Γ(M, V)} (he : IsFreeGenerator e) (x : X) (hx : x ∈ V) :
    Function.Bijective (fun r : X.presheaf.stalk x ↦
      r • TopCat.Presheaf.germ M.val.presheaf V x hx e) := by
  constructor
  · intro a b hab
    obtain ⟨A, hAV, hxA, a', ha⟩ := X.presheaf.exists_le_germ_eq a hx
    obtain ⟨B, hBV, hxB, b', hb⟩ := X.presheaf.exists_le_germ_eq b hx
    have hmA : TopCat.Presheaf.germ M.val.presheaf A x hxA
        (a' • M.presheaf.map (homOfLE hAV).op e) =
        a • TopCat.Presheaf.germ M.val.presheaf V x hx e := by
      rw [PresheafOfModules.germ_smul]
      change X.presheaf.germ A x hxA a' • _ = _
      rw [ha]
      exact congrArg (a • ·)
        (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE hAV) x hxA e)
    have hmB : TopCat.Presheaf.germ M.val.presheaf B x hxB
        (b' • M.presheaf.map (homOfLE hBV).op e) =
        b • TopCat.Presheaf.germ M.val.presheaf V x hx e := by
      rw [PresheafOfModules.germ_smul]
      change X.presheaf.germ B x hxB b' • _ = _
      rw [hb]
      exact congrArg (b • ·)
        (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE hBV) x hxB e)
    obtain ⟨W, hxW, iA, iB, hW⟩ := TopCat.Presheaf.germ_eq M.val.presheaf x hxA hxB
      _ _ (hmA.trans (hab.trans hmB.symm))
    have hWV : W ≤ V := (leOfHom iA).trans hAV
    have hcoeff : X.presheaf.map iA.op a' = X.presheaf.map iB.op b' := by
      apply (he.map hWV).smul_left_injective
      change M.presheaf.map iA.op _ = M.presheaf.map iB.op _ at hW
      simp only [map_smul, presheaf_map_map_apply] at hW
      rw [show iA ≫ homOfLE hAV = homOfLE hWV from Subsingleton.elim _ _,
        show iB ≫ homOfLE hBV = homOfLE hWV from Subsingleton.elim _ _] at hW
      exact hW
    rw [← ha, ← hb]
    exact X.presheaf.germ_ext W hxW iA iB hcoeff
  · intro z
    obtain ⟨W, hWV, hxW, z', hz⟩ :=
      TopCat.Presheaf.exists_le_germ_eq M.val.presheaf z hx
    obtain ⟨a, ha⟩ := (he.map hWV).exists_smul_eq z'
    refine ⟨X.presheaf.germ W x hxW a, ?_⟩
    change X.presheaf.germ W x hxW a • _ = z
    rw [← TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE hWV) x hxW e]
    rw [← PresheafOfModules.germ_smul]
    change TopCat.Presheaf.germ M.val.presheaf W x hxW
      (a • M.presheaf.map (homOfLE hWV).op e) = z
    rw [ha, hz]

set_option backward.isDefEq.respectTransparency false in
/-- The stalk-theoretic nonvanishing set equals the complement of the zero ideal's support.

Source: Stacks Project, Properties, Section 01PR and Lemma 01PW, local calculation
in its proof; Modules, Lemma 01CY.
(blueprint: lem-weil-pbc-section-nonvanishing-zero-locus).

Proof: Cover X by affine opens V on which M has a free generator e. Write the restriction
of s as f • e. The germ of e is a basis of M_x for every x in V, so the germ of s lies
in the maximal ideal times M_x precisely when the germ of f lies in the maximal ideal
of O_{X,x}. This is equivalent to f not being a unit in O_{X,x}, or x not lying in D(f).
On the other hand, homOfGlobalSection sends 1 to s, so its coefficient in the bases 1
and e is f. Hom.ideal_zeroLocus identifies its ideal on V with (f), whose support is
V minus D(f). Thus the two sets agree on each V, hence globally. The empty scheme and
the zero section satisfy the same local calculation, with no nonemptiness hypothesis. -/
theorem nonvanishingLocus_eq_compl_support_zeroLocus (X : Scheme.{u}) (M : X.Modules)
    [M.IsInvertible] (s : Γ(M, ⊤)) :
    nonvanishingLocus M s =
      ((Hom.zeroLocus (homOfGlobalSection M s)).support.compl : Set X) := by
  have := IsInvertible.sheafOfModules_isInvertible M
  ext x
  obtain ⟨V, hxV, -, e, he⟩ := exists_isFreeGenerator M (x := x) (W := ⊤) trivial
  let f := he.coeff (M.presheaf.map (homOfLE le_top).op s)
  let g := TopCat.Presheaf.germ M.val.presheaf V.1 x hxV e
  have hg := bijective_smul_germ M he x hxV
  have hspan : Submodule.span (X.presheaf.stalk x) ({g} : Set _) = ⊤ := by
    apply eq_top_iff.mpr
    intro z _
    obtain ⟨a, ha⟩ := hg.2 z
    exact Submodule.mem_span_singleton.mpr ⟨a, ha⟩
  have hsg : TopCat.Presheaf.germ M.val.presheaf ⊤ x trivial s =
      X.presheaf.germ V.1 x hxV f • g := by
    rw [← TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE le_top) x hxV s]
    have hf := he.coeff_smul (M.presheaf.map (homOfLE le_top).op s)
    change f • e = M.presheaf.map (homOfLE le_top).op s at hf
    change TopCat.Presheaf.germ M.val.presheaf V.1 x hxV
      (M.presheaf.map (homOfLE le_top).op s) = _
    rw [← hf, PresheafOfModules.germ_smul]
    rfl
  have hmem : TopCat.Presheaf.germ M.val.presheaf ⊤ x trivial s ∈
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) • (⊤ : Submodule (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk M.val.presheaf x)) ↔
      X.presheaf.germ V.1 x hxV f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [hsg, ← hspan, Submodule.mem_smul_span_singleton]
    constructor
    · rintro ⟨a, ha, heq⟩
      exact hg.1 heq ▸ ha
    · intro ha
      exact ⟨_, ha, rfl⟩
  have hbasic := basicOpen_coeff_eq (homOfGlobalSection M s) V he
  have hone : (homOfGlobalSection M s).app V.1 (unitSectionsEquiv V.1 1) =
      M.presheaf.map (homOfLE le_top).op s := homOfGlobalSection_app_one M s V.1
  have hbasic' : X.basicOpen f =
      V.1 ⊓ (Hom.zeroLocus (homOfGlobalSection M s)).support.compl :=
    (congrArg (fun a ↦ X.basicOpen (he.coeff a)) hone).symm.trans hbasic
  have hloc : x ∈ (Hom.zeroLocus (homOfGlobalSection M s)).support.compl ↔
      x ∈ X.basicOpen f := by
    rw [hbasic']
    exact ⟨fun h ↦ ⟨hxV, h⟩, fun h ↦ h.2⟩
  change _ ∉ _ ↔ _
  rw [hmem]
  change _ ∉ _ ↔ x ∈ (Hom.zeroLocus (homOfGlobalSection M s)).support.compl
  rw [hloc, X.mem_basicOpen f x hxV, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, not_not]

end AlgebraicGeometry.Scheme.Modules
