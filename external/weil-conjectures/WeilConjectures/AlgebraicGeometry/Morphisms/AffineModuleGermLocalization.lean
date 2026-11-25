/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # The module germ map on an affine open is a localization

## References

* Stacks Project, Tag 01IB (quasi-coherent modules on an affine scheme) and Tag 01HV (stalk of the
  associated sheaf)
-/

@[expose] public section

noncomputable section

universe u
open CategoryTheory Opposite TopCat.Presheaf TopologicalSpace
namespace AlgebraicGeometry.Scheme
open Modules

set_option backward.isDefEq.respectTransparency false in
/-- The affine section-to-stalk map of a quasi-coherent module is a localization. -/
theorem isLocalizedModule_affine_germ
    {L : Scheme.{u}} (N : L.Modules) (hqc : N.IsQuasicoherent)
    (V : L.Opens) (hV : IsAffineOpen V) (y : V) :
    letI : Module (L.presheaf.obj (op V))
        (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y) :=
      Module.compHom _ (L.presheaf.germ V y y.2).hom
    ∃ f : N.val.obj (op V) →ₗ[L.presheaf.obj (op V)]
        (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y),
      (∀ m, f m = N.presheaf.germ V y y.2 m) ∧
      IsLocalizedModule (hV.primeIdealOf y).asIdeal.primeCompl f := by
  classical
  let : N.IsQuasicoherent := hqc
  let U : L.affineOpens := ⟨V, hV⟩
  let x : L := y
  have hx : x ∈ U.1 := y.2
  let F := N
  let A := Γ(L, U.1)
  let S := (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let : Module (L.presheaf.stalk x) (F.presheaf.stalk x) :=
    inferInstanceAs (Module (L.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L)
      (F.val : _root_.PresheafOfModules (L.presheaf ⋙ forget₂ _ _)).presheaf x))
  let : Algebra A (L.presheaf.stalk x) := L.presheaf.algebra_section_stalk ⟨x, hx⟩
  let : Module A (F.presheaf.stalk x) :=
    Module.compHom _ (L.presheaf.germ U.1 x hx).hom
  let f : Γ(F, U.1) →ₗ[A] F.presheaf.stalk x :=
    { toFun := F.presheaf.germ U.1 x hx
      map_add' := map_add _
      map_smul' := fun r m ↦ PresheafOfModules.germ_smul (R := L.presheaf) F.val x U.1 hx r m }
  have hprime (g : A) (hxg : x ∈ L.basicOpen g) : g ∈ S := by
    change U.2.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen g
    rw [← U.2.fromSpec_preimage_basicOpen]
    change U.2.fromSpec (U.2.primeIdealOf ⟨x, hx⟩) ∈ L.basicOpen g
    rwa [U.2.fromSpec_primeIdealOf]
  have hloc : IsLocalizedModule S f := by
    refine ⟨?_, ?_, ?_⟩
    · intro s
      have := U.2.isLocalization_stalk ⟨x, hx⟩
      have hu : IsUnit (L.presheaf.germ U.1 x hx s.1) :=
        IsLocalization.map_units (L.presheaf.stalk x) s
      rw [Module.End.isUnit_iff]
      change Function.Bijective (fun m : F.presheaf.stalk x ↦
        L.presheaf.germ U.1 x hx s.1 • m)
      exact ⟨(fun a b h ↦ hu.smul_left_cancel.mp h), fun m ↦
        ⟨hu.unit⁻¹ • m, smul_inv_smul hu.unit m⟩⟩
    · intro y
      obtain ⟨V, hxV, m, rfl⟩ := F.presheaf.exists_germ_eq y
      obtain ⟨g, hgV, hxg⟩ := U.2.exists_basicOpen_le ⟨x, hxV⟩ hx
      obtain ⟨n, t, ht⟩ := exists_map_eq_pow_smul_of_isAffineOpen F U.2 g
        (F.presheaf.map (homOfLE hgV).op m)
      refine ⟨⟨t, ⟨g ^ n, S.pow_mem (hprime g hxg) n⟩⟩, ?_⟩
      have h := congrArg (F.presheaf.germ (L.basicOpen g) x hxg) ht
      erw [PresheafOfModules.germ_smul (R := L.presheaf) F.val] at h
      rw [_root_.map_pow] at h
      erw [L.presheaf.germ_res_apply, F.presheaf.germ_res_apply,
        F.presheaf.germ_res_apply] at h
      change L.presheaf.germ U.1 x hx (g ^ n) • F.presheaf.germ V x hxV m =
        F.presheaf.germ U.1 x hx t
      rw [_root_.map_pow]
      exact h.symm
    · intro m₁ m₂ hm
      obtain ⟨V, hxV, i₁, i₂, heq⟩ := F.presheaf.germ_eq x hx hx m₁ m₂ hm
      obtain ⟨g, hgV, hxg⟩ := U.2.exists_basicOpen_le ⟨x, hxV⟩ hx
      have hz : F.presheaf.map (homOfLE (L.basicOpen_le g)).op (m₁ - m₂) = 0 := by
        have h := congrArg (F.presheaf.map (homOfLE hgV).op) heq
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply] at h
        rw [map_sub, sub_eq_zero]
        convert h using 1
      obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isAffineOpen F U.2 g (m₁ - m₂) hz
      refine ⟨⟨g ^ n, S.pow_mem (hprime g hxg) n⟩, ?_⟩
      exact sub_eq_zero.mp ((smul_sub _ _ _).symm.trans hn)
  exact ⟨f, fun _ ↦ rfl, hloc⟩

end AlgebraicGeometry.Scheme
