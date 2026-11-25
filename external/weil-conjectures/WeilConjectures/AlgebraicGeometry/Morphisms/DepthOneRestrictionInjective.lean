/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.RingTheory.Depth

public import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.RingTheory.Regular.IsSMulRegular
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineSectionAssociatedStalk
public import Mathlib.RingTheory.Nakayama

/-! # Uniqueness of restriction across a depth-positive boundary

## References

* Stacks Project, Tags 0B3M (restriction avoiding weakly associated points), 05AR (associated and
  weakly associated points on a locally Noetherian scheme), and 00LL (depth zero and associated
  primes)
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

private theorem depth_zero_of_maximal_associated
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hm : IsAssociatedPrime (IsLocalRing.maximalIdeal R) M) :
    IsLocalRing.depth (R := R) M = 0 := by
  have : Nontrivial M := by
    by_contra h
    have : Subsingleton M := not_nontrivial_iff_subsingleton.mp h
    exact (not_isAssociatedPrime_of_subsingleton (I := IsLocalRing.maximalIdeal R)) hm
  have hM : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  rw [IsLocalRing.depth, Ideal.depth, ite_eq_right hM]
  apply le_antisymm _ zero_le
  apply sSup_le
  rintro n ⟨rs, hrs, hmem, rfl⟩
  cases rs with
  | nil => simp
  | cons x xs =>
    have hxreg := ((RingTheory.Sequence.isRegular_cons_iff M x xs).mp hrs).1
    have hx : x ∈ IsLocalRing.maximalIdeal R := hmem x (by simp)
    have hunion : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) :=
      Set.mem_iUnion.mpr ⟨IsLocalRing.maximalIdeal R, Set.mem_iUnion.mpr ⟨hm, hx⟩⟩
    rw [biUnion_associatedPrimes_eq_compl_regular R M] at hunion
    exact False.elim (hunion hxreg)

set_option backward.isDefEq.respectTransparency false in
/-- Sections are determined by restriction away from a depth-positive boundary. -/
theorem injective_restrictAdjunction_unit_app_of_depth_one
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (N : L.Modules)
    (hqc : N.IsQuasicoherent)
    (hsections : ∀ V : L.Opens, IsAffineOpen V →
      Module.Finite (L.presheaf.obj (op V)) (N.val.obj (op V)))
    (hdepth : ∀ y : L, y ∉ U →
      ∃ hfinite : Module.Finite (L.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y),
        letI := hfinite
        (1 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y))  :
    ∀ V : L.Opens,
      Function.Injective (((Modules.restrictAdjunction U.ι).unit.app N).app V) := by
  have haffine : ∀ (W : L.Opens), IsAffineOpen W →
      Function.Injective (((Modules.restrictAdjunction U.ι).unit.app N).app W) := by
    intro W hW s t hst
    by_contra hne
    obtain ⟨y, hyW, hass, hne⟩ :=
      exists_associated_stalk_germ_ne_of_isAffineOpen N hqc W hW
        (hsections W hW) s t hne
    have hyU : y ∈ U := by
      by_contra hyU
      obtain ⟨hfinite, hd⟩ := hdepth y hyU
      have := depth_zero_of_maximal_associated hass
      simp only [this] at hd
      exact (by simp : ¬ (1 : ℕ∞) ≤ 0) hd
    have hy : y ∈ U.ι ''ᵁ (U.ι ⁻¹ᵁ W) := by
      simpa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
        using (show y ∈ U ⊓ W from ⟨hyU, hyW⟩)
    apply hne
    rw [Modules.restrictAdjunction_unit_app_app] at hst
    have hg := congrArg (N.presheaf.germ _ y hy) hst
    change N.presheaf.germ _ y hy
        (N.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op s) =
      N.presheaf.germ _ y hy
        (N.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op t) at hg
    simpa only [germ_res_apply] using hg
  intro V s t hst
  apply TopCat.Presheaf.section_ext ⟨N.val.presheaf, N.isSheaf⟩ V s t
  intro x hxV
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    L.isBasis_affineOpens.exists_subset_of_mem_open hxV V.2
  have hWV' : W ≤ V := hWV
  have heq : N.val.presheaf.map (homOfLE hWV' : W ⟶ V).op s =
      N.val.presheaf.map (homOfLE hWV' : W ⟶ V).op t := by
    apply haffine W hW
    let f := (Modules.toPresheaf L).map ((Modules.restrictAdjunction U.ι).unit.app N)
    change f.app (op W) (N.presheaf.map (homOfLE hWV' : W ⟶ V).op s) =
      f.app (op W) (N.presheaf.map (homOfLE hWV' : W ⟶ V).op t)
    have hs := NatTrans.naturality_apply f (homOfLE hWV' : W ⟶ V).op s
    have ht := NatTrans.naturality_apply f (homOfLE hWV' : W ⟶ V).op t
    have heq := congrArg
      (((Modules.toPresheaf L).obj
        ((Modules.restrictFunctor U.ι ⋙ Modules.pushforward U.ι).obj N)).map
          (homOfLE hWV' : W ⟶ V).op) hst
    exact hs.trans (heq.trans ht.symm)
  have hg := congrArg (N.presheaf.germ W x hxW) heq
  change N.presheaf.germ V x hxV s = N.presheaf.germ V x hxV t
  change N.presheaf.germ W x hxW (N.presheaf.map (homOfLE hWV' : W ⟶ V).op s) =
    N.presheaf.germ W x hxW (N.presheaf.map (homOfLE hWV' : W ⟶ V).op t) at hg
  simpa only [germ_res_apply] using hg

end AlgebraicGeometry.Scheme
