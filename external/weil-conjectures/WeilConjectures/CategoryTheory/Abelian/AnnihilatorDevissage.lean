/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Data.Nat.Prime.Basic
public import WeilConjectures.CategoryTheory.Abelian.PrimeFactorDevissage

/-!
# Dévissage along an invertible annihilator

Let `G` be an object of an abelian category killed by a positive integer `n`, and let `p` be a
prime dividing `n`. The short exact sequence `0 ⟶ ker (p • 𝟙 G) ⟶ G ⟶ coim (p • 𝟙 G) ⟶ 0` has
its kernel killed by `p` and its coimage killed by `n / p`. By induction on `n`, a property `P`
which is stable under extensions and holds for zero objects and for objects killed by a prime
holds for every object killed by `n`. This variant restricts to a class `L` of objects stable
under these kernels and coimages, and only asks for primes `p` which are invertible in a ring
`R` in which `n` is invertible.

## Main statements

- `CategoryTheory.Abelian.nsmul_id_coimage_eq_zero`: if `G` is killed by `p * m`, then the
  coimage of `p • 𝟙 G` is killed by `m`.
- `CategoryTheory.Abelian.prop_of_nsmul_id_eq_zero_of_isUnit`: the dévissage.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Abelian

variable {C : Type*} [Category* C] [Abelian C]

/-- If `G` is killed by `p * m`, then the coimage `cokernel (kernel.ι (p • 𝟙 G))` of
multiplication by `p` is killed by `m`. -/
theorem nsmul_id_coimage_eq_zero (G : C) (p m : ℕ) (hkill : (p * m) • 𝟙 G = 0) :
    m • 𝟙 (cokernel (kernel.ι (p • 𝟙 G))) = 0 := by
  have hcomp : (m • 𝟙 G) ≫ (p • 𝟙 G) = 0 := by
    simpa [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      smul_smul, Nat.mul_comm] using hkill
  have h := Abelian.comp_coimage_π_eq_zero hcomp
  apply (cancel_epi (cokernel.π (kernel.ι (p • 𝟙 G)))).mp
  simpa [Abelian.coimage.π, Preadditive.nsmul_comp, Preadditive.comp_nsmul] using h

/-- **Dévissage along an invertible annihilator.** Let `L` be a class of objects stable under
`G ↦ ker (p • 𝟙 G)` and `G ↦ coim (p • 𝟙 G)`, and let `P` be a property which holds for zero
objects, is stable under extensions, and holds for the objects of `L` killed by a prime `p`
invertible in `R`. Then `P` holds for every object of `L` killed by a positive integer `n`
invertible in `R`.

Proof: induction on `n`. For `n = 1` the object is zero. Otherwise choose a prime `p ∣ n` and
write `n = p * m`; both `p` and `m` are invertible in `R`. In the short exact sequence
`0 ⟶ ker (p • 𝟙 G) ⟶ G ⟶ coim (p • 𝟙 G) ⟶ 0` the kernel is killed by `p` and the coimage by
`m < n` (`CategoryTheory.Abelian.nsmul_id_coimage_eq_zero`). -/
theorem prop_of_nsmul_id_eq_zero_of_isUnit {R : Type*} [CommRing R]
    (L P : C → Prop)
    (hker : ∀ (G : C), L G → ∀ p : ℕ, L (kernel (p • 𝟙 G)))
    (hcoker : ∀ (G : C), L G → ∀ p : ℕ, L (cokernel (kernel.ι (p • 𝟙 G))))
    (hzero : ∀ G, IsZero G → P G)
    (hseq : ∀ (E : ShortComplex C), E.ShortExact → P E.X₁ → P E.X₃ → P E.X₂)
    (hprime : ∀ p : ℕ, p.Prime → IsUnit (p : R) →
      ∀ G, L G → p • 𝟙 G = 0 → P G)
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : R))
    (G : C) (hG : L G) (hk : n • 𝟙 G = 0) : P G := by
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hone : n = 1
    · exact hzero G ((IsZero.iff_id_eq_zero _).2 (by simpa [hone] using hk))
    obtain ⟨p, hp, m, hpm⟩ := Nat.exists_prime_and_dvd hone
    have hm : 0 < m := by
      by_contra h
      have : m = 0 := Nat.eq_zero_of_not_pos h
      simp [this] at hpm
      omega
    have hmn : m < n := by
      rw [hpm]
      simpa using Nat.mul_lt_mul_of_pos_right hp.one_lt hm
    have hpunit : IsUnit (p : R) := by
      rw [hpm, Nat.cast_mul] at hu
      exact isUnit_of_mul_isUnit_left hu
    have hmunit : IsUnit (m : R) := by
      rw [hpm, Nat.cast_mul] at hu
      exact isUnit_of_mul_isUnit_right hu
    let φ := p • 𝟙 G
    let E := ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ))
      (cokernel.condition (kernel.ι φ))
    have hE : E.ShortExact := { exact := ShortComplex.exact_cokernel (kernel.ι φ) }
    exact hseq E hE
      (hprime p hp hpunit _ (hker G hG p) (nsmul_id_kernel_eq_zero G p))
      (ih m hmn hm hmunit _ (hcoker G hG p) (nsmul_id_coimage_eq_zero G p m (hpm ▸ hk)))

end CategoryTheory.Abelian
