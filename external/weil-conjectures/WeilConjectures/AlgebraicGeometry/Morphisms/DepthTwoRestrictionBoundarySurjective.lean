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

import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoAffineFiniteQuotientDepth
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-! # Existence of boundary germ extensions in depth two

## References

* Stacks Project, Tags 0AV8 and 0AVN, as used in Tag 0E9I
* Stacks Project, proof of Tag 0E9I, with Tags 0AV8, 0AVN and 05AM
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme

private theorem subsingleton_of_positive_local_depth
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (Q : Type u) [AddCommGroup Q] [Module R Q]
    (hd : ∀ (p : Ideal R) [p.IsPrime],
      ∃ hf : Module.Finite (Localization.AtPrime p) (LocalizedModule.AtPrime p Q),
        letI := hf
        (1 : ℕ∞) ≤ IsLocalRing.depth (R := Localization.AtPrime p)
          (LocalizedModule.AtPrime p Q)) : Subsingleton Q := by
  classical
  by_contra hn
  have : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hn
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R Q
  have : p.IsPrime := hp.isPrime
  obtain ⟨hf, hd⟩ := hd p
  let := hf
  let A := Localization.AtPrime p
  let T := LocalizedModule.AtPrime p Q
  have hass : IsLocalRing.maximalIdeal A ∈ associatedPrimes A T :=
    Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hp
  have hT : Nontrivial T := by
    by_contra h
    have : Subsingleton T := not_nontrivial_iff_subsingleton.mp h
    simp [associatedPrimes.eq_empty_of_subsingleton] at hass
  have ht : IsLocalRing.maximalIdeal A • (⊤ : Submodule A T) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator A T))).symm
  have hz : IsLocalRing.depth (R := A) T = 0 := by
    rw [IsLocalRing.depth, Ideal.depth, ite_eq_right ht]
    apply le_antisymm _ zero_le
    apply sSup_le
    rintro n ⟨rs, hrs, hm, rfl⟩
    cases rs with
    | nil => simp
    | cons x xs =>
      have hr := ((RingTheory.Sequence.isRegular_cons_iff T x xs).mp hrs).1
      have hu : x ∈ ⋃ p ∈ associatedPrimes A T, (p : Set A) :=
        Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨hass, hm x (by simp)⟩⟩
      rw [biUnion_associatedPrimes_eq_compl_regular A T] at hu
      exact (hu hr).elim
  rw [hz] at hd
  simp at hd

set_option backward.isDefEq.respectTransparency false in
/-- Boundary germs of the direct image lift across a depth-two boundary. -/
theorem surjective_restrictAdjunction_unit_stalk_of_depth_two
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
    (y : L) (hy : y ∉ U) :
    Function.Surjective ((stalkFunctor Ab.{u} y).map
      ((Modules.toPresheaf L).map ((Modules.restrictAdjunction U.ι).unit.app N))) := by
  classical
  have hyU : ¬ y ∈ U := hy
  intro t
  obtain ⟨V, hyV, hV, s, hs⟩ :=
    exists_mem_germ_eq_of_isBasis L.isBasis_affineOpens _ y t
  let R := L.presheaf.obj (op V)
  let P := (((Modules.pushforward U.ι).obj
    ((Modules.restrictFunctor U.ι).obj N)).val.obj (op V))
  let a : N.val.obj (op V) →ₗ[R] P :=
    (((Modules.restrictAdjunction U.ι).unit.app N).val.app (op V)).hom
  change P at s
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : Module.Finite R (N.val.obj (op V)) := hsections V hV
  let S : Submodule R P := LinearMap.range a ⊔ Submodule.span R {s}
  have hS : S.FG := (Submodule.fg_range a).sup (Submodule.fg_span_singleton s)
  have hMS : LinearMap.range a ≤ S := le_sup_left
  let K : Submodule R S := (LinearMap.range a).comap S.subtype
  have hQ : Subsingleton (S ⧸ K) :=
    subsingleton_of_positive_local_depth (S ⧸ K) fun p _ ↦
      depth_one_affine_finite_quotient_of_depth_two U N hqc hsections hdepth hinj
        V hV S hS hMS p
  have hsS : s ∈ S := (show Submodule.span R {s} ≤ S from le_sup_right)
    (Submodule.subset_span (by simp))
  have hsK : (⟨s, hsS⟩ : S) ∈ K := (Submodule.Quotient.mk_eq_zero K).mp (hQ.elim _ _)
  obtain ⟨r, hr⟩ := hsK
  refine ⟨germ N.val.presheaf V y hyV r, ?_⟩
  have he := stalkFunctor_map_germ_apply
    (f := (Modules.toPresheaf L).map ((Modules.restrictAdjunction U.ι).unit.app N))
    V y hyV r
  apply he.trans
  change (germ (C := Ab.{u})
    ((Modules.toPresheaf L).obj ((Modules.pushforward U.ι).obj
      ((Modules.restrictFunctor U.ι).obj N))) V y hyV) (a r) = t
  rw [show a r = s from hr]
  exact hs

end AlgebraicGeometry.Scheme
