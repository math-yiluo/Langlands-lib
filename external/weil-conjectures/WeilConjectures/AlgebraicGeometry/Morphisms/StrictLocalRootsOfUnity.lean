/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian

import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Algebra.Ring.GeomSum

/-! # Prime-to-characteristic roots of unity in a strict local ring

## References

* Stacks Project, Tags 0EYG and 09EV, root-of-unity input to the intermediate-root calculation
* Stacks Project, Tag 0EYG, final intermediate-field paragraph, and Tag 09EV, root-of-unity argument
-/

@[expose] public section

universe u
set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

/-- The roots of unity of invertible positive order in a strict local ring form
an order-n cyclic group, and a nonidentity root differs from one by a unit.

This is the Hensel-lifting input to the
intermediate-root calculation, extended to arbitrary strict local rings. -/
theorem strict_local_roots_of_unity
    (H : Type u) [CommRing H] [IsStrictlyHenselianLocalRing H]
    (n : ℕ) (hn : 0 < n ∧ IsUnit (n : H)) :
    Nat.card (rootsOfUnity n H) = n ∧ IsCyclic (rootsOfUnity n H) ∧
      ∀ ζ : rootsOfUnity n H, ζ ≠ 1 → IsUnit (((ζ : Hˣ) : H) - 1) := by
  classical
  let k := IsLocalRing.ResidueField H
  let q : H →+* k := IsLocalRing.residue H
  have hnk : IsUnit (n : k) := by simpa using hn.2.map q
  have : NeZero (n : k) := ⟨hnk.ne_zero⟩
  have : NeZero n := ⟨hn.1.ne'⟩
  let f : rootsOfUnity n H →* rootsOfUnity n k := restrictRootsOfUnity q n
  have hker : ∀ ζ : rootsOfUnity n H, f ζ = 1 → ζ = 1 := by
    intro ζ hz
    have hzq : q ((ζ : Hˣ) : H) = 1 := by
      simpa [f, restrictRootsOfUnity] using congrArg (fun a : rootsOfUnity n k ↦
        ((a : kˣ) : k)) hz
    have hsum : IsUnit (∑ i ∈ Finset.range n, (((ζ : Hˣ) : H) ^ i)) := by
      apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
      change q (∑ i ∈ Finset.range n, (((ζ : Hˣ) : H) ^ i)) ≠ 0
      simpa [map_sum, map_pow, hzq] using hnk.ne_zero
    have hpow := (mem_rootsOfUnity' n (ζ : Hˣ)).mp ζ.property
    have hzero : (((ζ : Hˣ) : H) - 1) *
        (∑ i ∈ Finset.range n, (((ζ : Hˣ) : H) ^ i)) = 0 := by
      rw [mul_geom_sum, hpow, sub_self]
    have heq : ((ζ : Hˣ) : H) = 1 := sub_eq_zero.mp
      (hsum.mul_right_cancel (hzero.trans (zero_mul _).symm))
    apply Subtype.ext
    exact Units.ext heq
  have hinj : Function.Injective f := (injective_iff_map_eq_one f).mpr hker
  have hsurj : Function.Surjective f := by
    intro ζ
    let p : Polynomial H := Polynomial.X ^ n - Polynomial.C 1
    have hp : p.Monic := Polynomial.monic_X_pow_sub_C _ hn.1.ne'
    have hpow := (mem_rootsOfUnity' n (ζ : kˣ)).mp ζ.property
    have hroot : Polynomial.aeval (((ζ : kˣ) : k)) p = 0 := by
      simp [p, hpow]
    have hd : Polynomial.aeval (((ζ : kˣ) : k)) p.derivative ≠ 0 := by
      simpa [p, Polynomial.derivative_X_pow] using
        mul_ne_zero hnk.ne_zero (pow_ne_zero (n - 1) (ζ : kˣ).ne_zero)
    have hensel : ∀ (p : Polynomial H), p.Monic →
        ∀ a₀ : IsLocalRing.ResidueField H, Polynomial.aeval a₀ p = 0 →
          Polynomial.aeval a₀ p.derivative ≠ 0 →
            ∃ a : H, p.IsRoot a ∧ IsLocalRing.residue H a = a₀ :=
      ((HenselianLocalRing.TFAE H).out 1 2).mp
        (inferInstance : HenselianLocalRing H)
    obtain ⟨a, ha, hqa⟩ := hensel p hp (((ζ : kˣ) : k)) hroot hd
    have hapow : a ^ n = 1 := by simpa [p, Polynomial.IsRoot, sub_eq_zero] using ha
    have hau : IsUnit a := by
      refine ⟨⟨a, a ^ (n - 1), ?_, ?_⟩, rfl⟩
      · rw [← pow_succ', Nat.sub_add_cancel (by omega), hapow]
      · rw [← pow_succ, Nat.sub_add_cancel (by omega), hapow]
    let ξ : rootsOfUnity n H := ⟨hau.unit, (mem_rootsOfUnity' n hau.unit).mpr
      (by simpa using hapow)⟩
    refine ⟨ξ, ?_⟩
    apply Subtype.ext
    apply Units.ext
    simpa [f, restrictRootsOfUnity, ξ, q] using hqa
  have hcardk := HasEnoughRootsOfUnity.natCard_rootsOfUnity k n
  have hcard : Nat.card (rootsOfUnity n H) = n :=
    (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).trans hcardk
  refine ⟨hcard, isCyclic_of_injective f hinj, ?_⟩
  intro ζ hζ
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  intro hz
  have hzq : q ((ζ : Hˣ) : H) = 1 := by
    simpa only [map_sub, map_one, sub_eq_zero] using hz
  apply hζ
  apply hker ζ
  apply Subtype.ext
  apply Units.ext
  simpa [f, restrictRootsOfUnity] using hzq

end AlgebraicGeometry.Scheme
