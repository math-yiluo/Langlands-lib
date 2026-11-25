/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Kummer characters on inertia and the tame relation

Let `Ω` be a field containing a primitive `N`-th root of unity `ζ`, and let a group `Γ` act on
`Ω` by ring automorphisms fixing `ζ`. A *Kummer element* for a character `χ : Γ → ℤ / N` is
`x ≠ 0` with `γ x = ζ ^ χ(γ) x`. Suppose an "inertia" predicate `P` on `Γ` is such that inertia
fixes every `N`-th root of a "local unit" (an element of a set `U ⊆ Ω`), and `x ^ N = u y ^ (N a)`
for a local unit `u` and an `N`-th root `y` of a "uniformizer". Then on inertia `χ = a κ`, where
`κ` is the Kummer character of `y`. If moreover an automorphism `φ` of `Ω` raising `ζ` to the
power `c`, preserving local units and multiplying `y ^ N` by a local unit normalises the situation
and leaves `χ` invariant, then `c χ = χ` on inertia
(`IsPrimitiveRoot.natCast_mul_eq_of_kummer`): this is the relation `φ τ φ⁻¹ = τ ^ c` of the tame
inertia group, seen on a character.

The input "inertia fixes `N`-th roots of local units" is
`Ideal.inertia_smul_eq_of_pow_eq_algebraMap`: for the integral closure `B` of a ring `R` in `Ω`,
an element `b ∈ B ∖ Q` with `b ^ N ∈ R` is fixed by the inertia group of `Q`, as soon as the
differences `ε - 1` of `N`-th roots of unity `ε ≠ 1` of `R` are units.
-/

@[expose] public section

namespace IsPrimitiveRoot

variable {Ω : Type*} [Field Ω] {N : ℕ} [NeZero N] {ζ : Ω} (hζ : IsPrimitiveRoot ζ N)

include hζ in
/-- Exponents of a primitive `N`-th root of unity are determined modulo `N`. -/
lemma intCast_eq_of_zpow_eq {i j : ℤ} (h : ζ ^ i = ζ ^ j) : (i : ZMod N) = j := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  have h1 : ζ ^ (i - j) = 1 := by rw [zpow_sub₀ hζ0, h, div_self (zpow_ne_zero _ hζ0)]
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact (hζ.zpow_eq_one_iff_dvd _).1 h1

include hζ in
/-- An `N`-th root of unity is a power of `ζ`. -/
lemma exists_pow_eq_div {a b : Ω} (hb : b ≠ 0) (h : a ^ N = b ^ N) : ∃ k : ℕ, a = ζ ^ k * b := by
  have : (a / b) ^ N = 1 := by rw [div_pow, h, div_self (pow_ne_zero _ hb)]
  obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one this
  exact ⟨k, by rw [hk, div_mul_cancel₀ _ hb]⟩

variable {Γ : Type*} (ρ : Γ → Ω ≃+* Ω) (U : Set Ω)

include hζ in
/-- On an element fixing the `N`-th roots of local units, a Kummer character `χ` with Kummer
element `x`, `x ^ N = u y ^ (N a)`, is `a` times the Kummer character of `y`. -/
lemma intCast_eq_mul_of_kummer {γ : Γ} (hγ : ∀ w : Ω, w ^ N ∈ U → ρ γ w = w) {x y : Ω}
    (hx : x ≠ 0) (hy : y ≠ 0) {a : ℤ} (hxy : x ^ N / (y ^ N) ^ a ∈ U) {m : ZMod N}
    (hχ : ρ γ x = ζ ^ m.val * x) {k : ℕ} (hk : ρ γ y = ζ ^ k * y) :
    m = (k : ZMod N) * (a : ZMod N) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
  have hya : y ^ a ≠ 0 := zpow_ne_zero _ hy
  set w := x / y ^ a with hw
  have hwN : w ^ N ∈ U := by
    rwa [hw, div_pow, ← zpow_natCast (y ^ a), ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  have hxw : x = w * y ^ a := by rw [hw, div_mul_cancel₀ _ hya]
  have h1 : ρ γ x = ζ ^ ((k : ℤ) * a) * x := by
    rw [hxw, map_mul, hγ w hwN, map_zpow₀, hk, mul_zpow, ← zpow_natCast ζ k, ← zpow_mul]
    ring
  rw [hχ, ← zpow_natCast] at h1
  have := hζ.intCast_eq_of_zpow_eq (mul_right_cancel₀ hx h1)
  rw [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_mul, Int.cast_natCast] at this
  exact this

include hζ in
/-- **The tame relation on Kummer characters.** Let `χ : Γ → ℤ / N` be a Kummer character with
Kummer element `x`, `x ^ N = u y ^ (N a)` for a local unit `u`. Let `φ` be an automorphism of `Ω`
with `φ ζ = ζ ^ c`, preserving local units, with `φ (y ^ N) = u' y ^ N` for a local unit `u'`,
and such that conjugation by `φ` preserves `Γ` and `χ`. Then `c χ(γ) = χ(γ)` for every `γ`
fixing the `N`-th roots of local units. -/
theorem natCast_mul_eq_of_kummer (χ : Γ → ZMod N) {x y : Ω} (hx : x ≠ 0) (hy : y ≠ 0) {a : ℤ}
    (hxy : x ^ N / (y ^ N) ^ a ∈ U) (hχ : ∀ γ, ρ γ x = ζ ^ (χ γ).val * x)
    (hyN : ∀ γ, ρ γ (y ^ N) = y ^ N) (φ : Ω ≃+* Ω) {c : ℕ} (hφζ : φ ζ = ζ ^ c)
    (hφU : ∀ u ∈ U, φ u ∈ U) (hφy : φ y ^ N / y ^ N ∈ U)
    (hconj : ∀ γ, ∃ γ', (∀ w, ρ γ' w = φ.symm (ρ γ (φ w))) ∧ χ γ' = χ γ)
    {γ : Γ} (hγ : ∀ w : Ω, w ^ N ∈ U → ρ γ w = w) :
    (c : ZMod N) * χ γ = χ γ := by
  have hκ (γ : Γ) : ∃ k : ℕ, ρ γ y = ζ ^ k * y :=
    hζ.exists_pow_eq_div hy (by rw [← map_pow, hyN])
  obtain ⟨γ', hγ', hχγ'⟩ := hconj γ
  have hγ'U : ∀ w : Ω, w ^ N ∈ U → ρ γ' w = w := fun w hw ↦ by
    rw [hγ', hγ (φ w) (by rw [← map_pow]; exact hφU _ hw), RingEquiv.symm_apply_apply]
  obtain ⟨k, hk⟩ := hκ γ
  obtain ⟨k', hk'⟩ := hκ γ'
  have h := hζ.intCast_eq_mul_of_kummer ρ U hγ hx hy hxy (hχ γ) hk
  have h' := hζ.intCast_eq_mul_of_kummer ρ U hγ'U hx hy hxy (hχ γ') hk'
  -- `ρ γ (φ y) = ζ ^ (c k') φ y` and `ρ γ (φ y) = ζ ^ k φ y`
  have hφy0 : φ y ≠ 0 := (map_ne_zero φ).2 hy
  have e1 : ρ γ (φ y) = ζ ^ (c * k') * φ y := by
    have : φ (ρ γ' y) = ρ γ (φ y) := by rw [hγ', RingEquiv.apply_symm_apply]
    rw [← this, hk', map_mul, map_pow, hφζ, ← pow_mul]
  have e2 : ρ γ (φ y) = ζ ^ k * φ y := by
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne N)
    have hw : ρ γ (φ y / y) = φ y / y := hγ _ (by rwa [div_pow])
    rw [map_div₀, hk, div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hζ0) hy) hy] at hw
    apply mul_right_cancel₀ hy
    rw [hw]
    ring
  have hck : ((c * k' : ℕ) : ZMod N) = k := by
    have := mul_right_cancel₀ hφy0 (e1.symm.trans e2)
    have := hζ.intCast_eq_of_zpow_eq (i := ((c * k' : ℕ) : ℤ)) (j := (k : ℤ))
      (by rw [zpow_natCast, zpow_natCast, this])
    exact_mod_cast this
  calc (c : ZMod N) * χ γ = c * χ γ' := by rw [hχγ']
    _ = ((c * k' : ℕ) : ZMod N) * a := by rw [h']; push_cast; ring
    _ = χ γ := by rw [hck, h]

end IsPrimitiveRoot

namespace Ideal

variable {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω] {G : Type*} [Group G]
  [MulSemiringAction G Ω] [SMulCommClass G R Ω]

/-- **Inertia fixes `N`-th roots of units.** Let `B` be the integral closure of `R` in `Ω` and `Q`
a prime of `B`. An element `σ` of the inertia group of `Q` moving `b ∈ B ∖ Q` to `ε b`, where
`ε` is the image of an element `ε₀` of `R` such that `ε₀ - 1` is a unit unless `ε₀ = 1`, fixes `b`:
`σ b - b = (ε - 1) b ∈ Q`. -/
lemma inertia_smul_eq_of_smul_eq_mul (Q : Ideal (integralClosure R Ω)) [Q.IsPrime] {σ : G}
    (hσ : σ ∈ Q.inertia G) {b : integralClosure R Ω} (hb : b ∉ Q) {ε₀ : R}
    (hε₀ : ε₀ ≠ 1 → IsUnit (ε₀ - 1)) (h : σ • (b : Ω) = algebraMap R Ω ε₀ * b) :
    σ • (b : Ω) = b := by
  by_cases hε : ε₀ = 1
  · rw [h, hε, map_one, one_mul]
  have hmem : σ • b - b ∈ Q := hσ b
  have hσb : σ • b = algebraMap R (integralClosure R Ω) ε₀ * b := Subtype.ext h
  rw [hσb, ← sub_one_mul, ← map_one (algebraMap R _), ← map_sub] at hmem
  have hu : IsUnit (algebraMap R (integralClosure R Ω) (ε₀ - 1)) := (hε₀ hε).map _
  exact absurd ((Ideal.IsPrime.mem_or_mem ‹_› hmem).resolve_right hb)
    fun h' ↦ Ideal.IsPrime.ne_top ‹_› (Q.eq_top_of_isUnit_mem h' hu)

/-- **Inertia fixes `N`-th roots of local units.** Let `Q` be a prime of the integral closure of
`R` in `Ω`, and `ζ ∈ R` with primitive image in `Ω` such that `ζ ^ k - 1` is a unit unless
`ζ ^ k = 1`. If `(w s) ^ N = r` with `r, s ∈ R`, `r ∉ Q` and `s ≠ 0` in `Ω`, then the inertia
group of `Q` fixes `w`. -/
theorem inertia_smul_eq_of_pow_eq (Q : Ideal (integralClosure R Ω)) [Q.IsPrime] {σ : G}
    (hσ : σ ∈ Q.inertia G) {N : ℕ} [NeZero N] {ζ : R}
    (hζ : IsPrimitiveRoot (algebraMap R Ω ζ) N) (hζu : ∀ k : ℕ, ζ ^ k ≠ 1 → IsUnit (ζ ^ k - 1))
    {w : Ω} {r s : R} (hr : algebraMap R (integralClosure R Ω) r ∉ Q)
    (hs : algebraMap R Ω s ≠ 0) (hw : (w * algebraMap R Ω s) ^ N = algebraMap R Ω r) :
    σ • w = w := by
  have hint : IsIntegral R (w * algebraMap R Ω s) :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne N)) (hw ▸ isIntegral_algebraMap)
  let b : integralClosure R Ω := ⟨_, hint⟩
  have hbN : b ^ N = algebraMap R (integralClosure R Ω) r := Subtype.ext (by
    change (w * algebraMap R Ω s) ^ N = algebraMap R Ω r
    exact hw)
  have hb : b ∉ Q := fun h ↦ hr (hbN ▸ Q.pow_mem_of_mem h N (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hb0 : (b : Ω) ≠ 0 := fun h ↦ hb (by
    rw [show b = 0 from Subtype.ext h]
    exact Q.zero_mem)
  obtain ⟨k, hk⟩ := hζ.exists_pow_eq_div hb0 (a := σ • (b : Ω)) (by
    rw [← smul_pow', show (b : Ω) ^ N = algebraMap R Ω r from hw, smul_algebraMap])
  have := inertia_smul_eq_of_smul_eq_mul Q hσ hb (hζu k) (by rw [hk, map_pow])
  change σ • (w * algebraMap R Ω s) = w * algebraMap R Ω s at this
  rw [smul_mul', smul_algebraMap] at this
  exact mul_right_cancel₀ hs this

end Ideal
