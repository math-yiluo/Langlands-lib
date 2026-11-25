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

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime

import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoAffineBoundarySubmoduleDepth
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoAffineRestrictionSourceDepth
import WeilConjectures.RingTheory.DepthInSES
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.Finiteness

/-! # Positive depth of finite quotients of restriction sections

## References

* Stacks Project, surjectivity argument of Tag 0AV8, as used in 0E9I
* Tags 0AVN, 05AM, 00LL and 00LX
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

private theorem depth_equiv {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {P : Type u} [AddCommGroup P] [Module R P] [Module.Finite R P]
    (e : M ≃ₗ[R] P) : IsLocalRing.depth (R := R) M = IsLocalRing.depth (R := R) P := by
  have hmap : (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)).map e.toLinearMap =
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R P) := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective]
  have htop : (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) = ⊤) ↔
      (IsLocalRing.maximalIdeal R • (⊤ : Submodule R P) = ⊤) := by
    constructor
    · intro h
      rw [← hmap, h]
      simp
    · intro h
      rw [← hmap] at h
      exact (Submodule.map_eq_top_iff.mp h)
  unfold IsLocalRing.depth Ideal.depth
  split_ifs with hM hP hP
  · rfl
  · exact (hP (htop.mp hM)).elim
  · exact (hM (htop.mpr hP)).elim
  · congr 1
    ext n
    constructor
    · rintro ⟨rs, hreg, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).mp hreg, hmem, rfl⟩
    · rintro ⟨rs, hreg, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).mpr hreg, hmem, rfl⟩

private theorem depth_subsingleton {R : Type u} [CommRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Subsingleton M] :
    IsLocalRing.depth (R := R) M = ⊤ := by
  unfold IsLocalRing.depth Ideal.depth
  rw [ite_eq_left (Subsingleton.elim _ _)]

private theorem depth_one_of_short_exact {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    {A B C : Type u} [AddCommGroup A] [Module R A] [Module.Finite R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B]
    [AddCommGroup C] [Module R C] [Module.Finite R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hex : Function.Exact f g) (hg : Function.Surjective g)
    (hA : (2 : ℕ∞) ≤ IsLocalRing.depth (R := R) A)
    (hB : (1 : ℕ∞) ≤ IsLocalRing.depth (R := R) B) :
    (1 : ℕ∞) ≤ IsLocalRing.depth (R := R) C := by
  classical
  cases subsingleton_or_nontrivial C with
  | inl hC =>
    let := hC
    rw [depth_subsingleton C]
    exact le_top
  | inr hC =>
    let := hC
    have : Nontrivial B := hg.nontrivial
    cases subsingleton_or_nontrivial A with
    | inl hA0 =>
      let := hA0
      have hgI : Function.Injective g := by
        intro x y hxy
        have hz : g (x - y) = 0 := by simp [hxy]
        obtain ⟨a, ha⟩ := (hex (x - y)).mp hz
        have : x - y = 0 := by rw [← ha, Subsingleton.elim a 0, map_zero]
        exact sub_eq_zero.mp this
      rw [← depth_equiv (LinearEquiv.ofBijective g ⟨hgI, hg⟩)]
      exact hB
    | inr hA0 =>
      let := hA0
      have hd := (IsLocalRing.depth_in_short_exact f g hf hex hg).2.1
      apply le_trans (le_min hB ?_) hd
      have hsub := tsub_le_tsub_right hA 1
      exact le_trans (by decide : (1 : ℕ∞) ≤ 2 - 1) hsub

/-- Every finite intermediate extension has a quotient of positive local depth. -/
theorem depth_one_affine_finite_quotient_of_depth_two
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (N : L.Modules)
    (hqc : N.IsQuasicoherent)
    (hsections : ∀ V : L.Opens, IsAffineOpen V →
      Module.Finite (L.presheaf.obj (op V)) (N.val.obj (op V)))
    (hdepth : ∀ y : L, y ∉ U →
      ∃ hfinite : Module.Finite (L.presheaf.stalk y)
            (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := L) N.val.presheaf y)) 
    (hinj : ∀ V : L.Opens,
      Function.Injective (((Modules.restrictAdjunction U.ι).unit.app N).app V))
    (V : L.Opens) (hV : IsAffineOpen V)
    (S : Submodule (L.presheaf.obj (op V))
      (((Modules.pushforward U.ι).obj
        ((Modules.restrictFunctor U.ι).obj N)).val.obj (op V)))
    (hS : S.FG)
    (hMS : LinearMap.range
      (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom ≤ S)
    (p : Ideal (L.presheaf.obj (op V))) [p.IsPrime] :
    ∃ hfinite : Module.Finite (Localization.AtPrime p)
      (LocalizedModule.AtPrime p
        (S ⧸ (LinearMap.range
          (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom).comap
            S.subtype)),
      letI := hfinite
      (1 : ℕ∞) ≤ IsLocalRing.depth (R := Localization.AtPrime p)
        (LocalizedModule.AtPrime p
          (S ⧸ (LinearMap.range
            (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom).comap
              S.subtype)) := by
  classical
  let R := L.presheaf.obj (op V)
  let K : Submodule R S := (LinearMap.range
    (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom).comap S.subtype
  let Q := S ⧸ K
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : Module.Finite R S := Module.Finite.of_fg hS
  have : Module.Finite (Localization.AtPrime p) (LocalizedModule.AtPrime p Q) :=
    inferInstance
  refine ⟨inferInstance, ?_⟩
  change (1 : ℕ∞) ≤ IsLocalRing.depth (R := Localization.AtPrime p)
    (LocalizedModule.AtPrime p Q)
  obtain ⟨hK, hinside, houtside⟩ := affine_restriction_source_depth_comparison
    U N hqc hsections hdepth hinj V hV S hS hMS p
  let := hK
  by_cases hy : hV.fromSpec ⟨p, inferInstance⟩ ∈ U
  · have := hinside hy
    rw [depth_subsingleton (LocalizedModule.AtPrime p Q)]
    exact le_top
  · obtain ⟨hfiniteS, hSp⟩ := depth_one_affine_boundary_submodule U N hqc V hV S hS p hy
    let := hfiniteS
    let f := LocalizedModule.map p.primeCompl K.subtype
    let g := LocalizedModule.map p.primeCompl K.mkQ
    apply depth_one_of_short_exact f g
    · exact LocalizedModule.map_injective _ _ K.subtype_injective
    · exact LocalizedModule.map_exact _ _ _ (LinearMap.exact_subtype_mkQ K)
    · exact LocalizedModule.map_surjective _ _ K.mkQ_surjective
    · exact houtside hy
    · exact hSp

end AlgebraicGeometry.Scheme
