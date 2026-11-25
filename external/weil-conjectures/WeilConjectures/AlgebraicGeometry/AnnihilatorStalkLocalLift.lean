/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor

import WeilConjectures.AlgebraicGeometry.AnnihilatorAffineCriterion
import all WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion

/-! # Local representatives of annihilated stalk elements
Source: Stacks Project, Tag 01PO, final sentence of the proof.
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite
open scoped AlgebraicGeometry
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- An annihilated germ has a representative annihilated by every local ideal section.
Source: Stacks Project, Tag 01PO, proof of (3), the omitted finite-generator argument.
(blueprint: lem-weil-pbc-annihilator-stalk-local-lift).

Proof: choose an affine neighborhood U of x and write F|U = M tilde, J|U = I tilde.
The finite-type ideal has generators g_1,...,g_t. Represent s by m/d in the
localization of M at the prime corresponding to x, with d outside that prime.
The hypothesis applied to each generator gives g_i m/d = 0. Clear a denominator
t_i outside the prime for each equality, and set t to their product. Then tm is
killed by every g_i, hence by I. On the principal neighborhood D(td), the section
(tm)/(td) has germ m/d = s and is killed by the restricted ideal. The affine
annihilation criterion gives the stated local annihilation condition. If I = 0,
use the empty product t = 1. The neighborhood may be shrunk to any initial affine
neighborhood; no choice of a global sheaf or morphism is needed.
-/
theorem annihilator_stalk_local_lift (X : Scheme.{u}) (J : X.IdealSheafData)
    [J.toModules.IsFiniteType] (F : X.Modules) [F.IsQuasicoherent] (x : X)
    (s : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)
    (hs : ∀ (U : X.Opens) (hx : x ∈ U), ∀ a ∈ J.idealOfOpens U,
      X.presheaf.germ U x hx a • s = 0) :
    ∃ (U : X.Opens) (hx : x ∈ U) (t : Γ(F, U)),
      F.presheaf.germ U x hx t = s ∧
      ∀ (V : X.Opens) (h : V ≤ U), ∀ a ∈ J.idealOfOpens V,
        a • F.presheaf.map (homOfLE h).op t = 0 := by
  classical
  obtain ⟨V, hxV, t, ht⟩ := F.presheaf.exists_germ_eq s
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let m := F.presheaf.map (homOfLE hUV).op t
  have hm : F.presheaf.germ U x hxU m = s := by
    rw [show F.presheaf.germ U x hxU m = F.presheaf.germ V x hxV t from
      F.presheaf.germ_res_apply (homOfLE hUV) x hxU t, ht]
  have := SheafOfModules.isQuasicoherent_unit (R := J.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      ((SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit J.subscheme.ringCatSheaf)) :=
    Scheme.Modules.isQuasicoherent_pushforward_of_isClosedImmersion J.subschemeι _
  have : J.toModules.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_kernel J.toPushforwardSubscheme
  have : Module.Finite Γ(X, U) Γ(J.toModules, U) :=
    Scheme.Modules.finite_sections_of_finiteType J.toModules hU
  have hfg : (J.ideal ⟨U, hU⟩).FG := by
    have h := (Module.Finite.fg_top (R := Γ(X, U)) (M := Γ(J.toModules, U))).map
      (J.toModulesι.val.app (op U)).hom
    have heq : (⊤ : Submodule Γ(X, U) Γ(J.toModules, U)).map
        (J.toModulesι.val.app (op U)).hom = J.ideal ⟨U, hU⟩ := by
      ext a
      rw [Submodule.map_top, LinearMap.mem_range]
      change (∃ y, J.toModulesι.app U y = a) ↔ a ∈ J.ideal ⟨U, hU⟩
      exact Set.ext_iff.mp (J.range_toModulesι_app ⟨U, hU⟩) a
    rw [heq] at h
    exact h
  obtain ⟨g, hg⟩ := hfg
  have hkill : ∀ a ∈ g, ∃ (W : X.Opens) (hxW : x ∈ W) (hWU : W ≤ U),
      X.presheaf.map (homOfLE hWU).op a •
        F.presheaf.map (homOfLE hWU).op m = 0 := by
    intro a ha
    have haJ : a ∈ J.idealOfOpens U := by
      rw [J.idealOfOpens_eq_ideal ⟨U, hU⟩, ← hg]
      exact Submodule.subset_span ha
    have heq : F.presheaf.germ U x hxU (a • m) = F.presheaf.germ U x hxU 0 := by
      erw [PresheafOfModules.germ_smul (R := X.presheaf) F.val, hm,
        hs U hxU a haJ, map_zero]
    obtain ⟨W, hxW, i, j, he⟩ := F.presheaf.germ_eq x hxU hxU (a • m) 0 heq
    refine ⟨W, hxW, i.le, ?_⟩
    simpa only [F.map_smul, map_zero] using! he
  choose W hxW hWU hWkill using fun a : (g : Set Γ(X, U)) ↦ hkill a a.property
  let V' : X.Opens := U ⊓ ⨅ a : (g : Set Γ(X, U)), W a
  have hxV' : x ∈ V' := by
    exact ⟨hxU, by
      change x ∈ ((⨅ a : (g : Set Γ(X, U)), W a) : X.Opens)
      rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
      exact hxW⟩
  obtain ⟨Z, hZ, hxZ, hZV'⟩ := exists_isAffineOpen_mem_and_subset hxV'
  have hZU : Z ≤ U := hZV'.trans inf_le_left
  let n := F.presheaf.map (homOfLE hZU).op m
  have hgen : ∀ a ∈ g, X.presheaf.map (homOfLE hZU).op a • n = 0 := by
    intro a ha
    have hZW : Z ≤ W ⟨a, ha⟩ :=
      hZV'.trans (inf_le_right.trans (iInf_le W (⟨a, ha⟩ : (g : Set Γ(X, U)))))
    have he := congrArg (F.presheaf.map (homOfLE hZW).op) (hWkill ⟨a, ha⟩)
    rw [F.map_smul, map_zero] at he
    convert he using 1
    simp only [n, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  let K : Ideal Γ(X, Z) :=
    LinearMap.ker (LinearMap.toSpanSingleton Γ(X, Z) Γ(F, Z) n)
  have hle : J.ideal ⟨Z, hZ⟩ ≤ K := by
    rw [← J.map_ideal (U := ⟨Z, hZ⟩) (V := ⟨U, hU⟩) hZU,
      Ideal.map_le_iff_le_comap, ← hg]
    apply Submodule.span_le.mpr
    intro a ha
    exact hgen a ha
  refine ⟨Z, hxZ, n, ?_, ?_⟩
  · exact (F.presheaf.germ_res_apply (homOfLE hZU) x hxZ m).trans hm
  · apply (annihilator_affine_criterion X J F ⟨Z, hZ⟩ n).mpr
    intro a ha
    exact hle ha

end AlgebraicGeometry
