/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootInvariants
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

import WeilConjectures.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity

/-!
# Uniqueness of rotations between points of the punctured root algebra

## References

* Stacks Project, Tags 0EYG and 09EV
-/

@[expose] public section
universe u
set_option autoImplicit false
namespace AlgebraicGeometry.Scheme

/-- Field valued points of the punctured root algebra differ by a unique rotation. -/
theorem strict_local_root_torsor_unique
    (H : Type u) [CommRing H] [IsStrictlyHenselianLocalRing H]
    [IsRegularLocalRing H] (h : H)
    [IsRegularLocalRing (H ⧸ Ideal.span {h})]
    (hh : IsSMulRegular H h) (hhm : h ∈ IsLocalRing.maximalIdeal H)
    (n : ℕ) (hn : 0 < n ∧ IsUnit (n : H)) :
    let C := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)
    ∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C h) ≠ 0 →
      ∃! ζ : rootsOfUnity n H,
        a.comp (rootRotation H h n ζ).toRingHom = b := by
  classical
  have _ := hh
  have _ := hhm
  intro C Ω _ a b hab hnonzero
  let p : Polynomial H := Polynomial.X ^ n - Polynomial.C h
  let t : C := AdjoinRoot.root p
  let q : H →+* Ω := a.comp (algebraMap H C)
  have ht : t ^ n = algebraMap H C h := by
    simpa [t, p, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using AdjoinRoot.eval₂_root p
  have hat : a t ≠ 0 := by
    intro hz
    apply hnonzero
    rw [← ht, map_pow, hz, zero_pow hn.1.ne']
  have hbt : b t ^ n = a t ^ n := by
    rw [← map_pow, ht, ← RingHom.comp_apply, ← hab, RingHom.comp_apply, ← ht, map_pow]
  have : NeZero n := ⟨hn.1.ne'⟩
  obtain ⟨hcard, _, hsep⟩ := strict_local_roots_of_unity H n hn
  let f : rootsOfUnity n H →* rootsOfUnity n Ω := restrictRootsOfUnity q n
  have hker : ∀ ζ : rootsOfUnity n H, f ζ = 1 → ζ = 1 := by
    intro ζ hz
    by_contra hζ
    have hunit := (hsep ζ hζ).map q
    have hzq : q ((ζ : Hˣ) : H) = 1 := by
      simpa [f, restrictRootsOfUnity] using
        congrArg (fun x : rootsOfUnity n Ω ↦ ((x : Ωˣ) : Ω)) hz
    exact hunit.ne_zero (by rw [map_sub, hzq, map_one, sub_self])
  have hinj : Function.Injective f := (injective_iff_map_eq_one f).mpr hker
  have hc : Nat.card (rootsOfUnity n Ω) ≤ Nat.card (rootsOfUnity n H) := by
    rw [hcard]
    exact card_rootsOfUnity Ω n
  have hsurj : Function.Surjective f := (hinj.bijective_of_nat_card_le hc).2
  have hratio : (b t / a t) ^ n = 1 := by
    rw [div_pow, hbt, div_self (pow_ne_zero n hat)]
  let ξ : rootsOfUnity n Ω := rootsOfUnity.mkOfPowEq (b t / a t) hratio
  obtain ⟨ζ, hζ⟩ := hsurj ξ
  have hzq : q ((ζ : Hˣ) : H) = b t / a t := by
    simpa [f, restrictRootsOfUnity, ξ] using
      congrArg (fun x : rootsOfUnity n Ω ↦ ((x : Ωˣ) : Ω)) hζ
  have hrot (η : rootsOfUnity n H) :
      rootRotation H h n η t = algebraMap H C ((η : Hˣ) : H) * t := by
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have heq : a.comp (rootRotation H h n ζ).toRingHom = b := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro x
      change a (rootRotation H h n ζ (algebraMap H C x)) = b (algebraMap H C x)
      rw [AlgHom.commutes]
      exact RingHom.congr_fun hab x
    · change a (rootRotation H h n ζ t) = b t
      rw [hrot, map_mul]
      change q ((ζ : Hˣ) : H) * a t = b t
      rw [hzq, div_mul_cancel₀ _ hat]
  refine ⟨ζ, heq, ?_⟩
  intro η hη
  apply hinj
  apply Subtype.ext
  apply Units.ext
  have hηt := RingHom.congr_fun hη t
  have hζt := RingHom.congr_fun heq t
  have hval : q ((η : Hˣ) : H) = q ((ζ : Hˣ) : H) := by
    apply mul_right_cancel₀ hat
    change a (algebraMap H C ((η : Hˣ) : H)) * a t =
      a (algebraMap H C ((ζ : Hˣ) : H)) * a t
    have he : a (rootRotation H h n η t) = a (rootRotation H h n ζ t) :=
      hηt.trans hζt.symm
    simpa only [hrot, map_mul] using he
  simpa [f, restrictRootsOfUnity] using hval

end AlgebraicGeometry.Scheme
