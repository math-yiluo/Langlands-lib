/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Successor step for prime-power torsion induction. -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace ModuleCat

/--
The successor case in the prime-power extension induction.

Source: Stacks Project, Tag 0F08 (cyclic-coefficient reduction); the explicit
cyclic short exact sequence argument below is an explicit refinement.

Proof: Put `a = r ^ e`. Since `r` is prime, both `r` and `a` are positive.
Define `i : ℤ/aℤ → ℤ/(a*r)ℤ` by `[x] ↦ [r*x]` and
`q : ℤ/(a*r)ℤ → ℤ/rℤ` by `[y] ↦ [y]`. Changing `x` by a multiple of `a`
changes `r*x` by a multiple of `a*r`, so `i` is well-defined; reduction `q`
is well-defined since `r` divides `a*r`. These additive maps are integer-linear.
If `i([x]) = 0`, divisibility `a*r ∣ r*x` and cancellation of the nonzero
integer `r` give `a ∣ x`, proving injectivity. Every integer representative
of a class modulo `r` is also a representative modulo `a*r`, so `q` is
surjective. Moreover `q([y]) = 0` precisely when `r ∣ y`, precisely when
`[y]` is in the image of `i`; hence the sequence is exact. Lift the maps and
modules by `ULift` and use `r ^ (e + 1) = a*r` to identify its middle term.
Apply `hext` to this short exact sequence, using `hind` and `hprime` on its
end terms and `hiso` for the canonical identifications. For `e = 0`, the
sequence is `0 → ℤ/rℤ → ℤ/rℤ` with identity quotient, so the same argument
also covers the boundary case.
(blueprint: lem-sbc-finite-torsion-prime-power-successor)
-/
theorem finite_torsion_prime_power_successor
    (P : ModuleCat.{u + 1} (ULift.{u + 1} ℤ) → Prop)
    (hiso : ∀ {A B}, (A ≅ B) → P A → P B)
    (hext : ∀ (S : ShortComplex (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))),
      S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (r e : ℕ) (hr : r.Prime)
    (hind : P (ModuleCat.of (ULift.{u + 1} ℤ) (ULift.{u + 1} (ZMod (r ^ e)))))
    (hprime : P (ModuleCat.of (ULift.{u + 1} ℤ) (ULift.{u + 1} (ZMod r)))) :
    P (ModuleCat.of (ULift.{u + 1} ℤ) (ULift.{u + 1} (ZMod (r ^ (e + 1))))) := by
  let a := r ^ e
  let f : ℤ →+ ZMod (a * r) :=
    (AddMonoidHom.mulLeft (r : ZMod (a * r))).comp (Int.castAddHom _)
  have hf : f a = 0 := by
    change (r : ZMod (a * r)) * (a : ℤ) = 0
    rw [Int.cast_natCast, ← Nat.cast_mul, mul_comm r a, ZMod.natCast_self]
  let i₀ : ZMod a →+ ZMod (a * r) := ZMod.lift a ⟨f, hf⟩
  let q₀ : ZMod (a * r) →+* ZMod r := ZMod.castHom (dvd_mul_left r a) _
  have hi_cast (z : ℤ) : i₀ (z : ZMod a) = (r : ZMod (a * r)) * z := by
    exact ZMod.lift_coe a ⟨f, hf⟩ z
  have hi : Function.Injective i₀ := by
    apply (injective_iff_map_eq_zero i₀).mpr
    intro x hx
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
    rw [hi_cast] at hx
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd z a).mpr
    have hz' : ((a * r : ℕ) : ℤ) ∣ (r : ℤ) * z := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (a * r)).mp
      simpa [f, Int.cast_mul] using hx
    rw [Nat.cast_mul, mul_comm (a : ℤ) (r : ℤ)] at hz'
    exact (mul_dvd_mul_iff_left (by exact_mod_cast hr.ne_zero)).mp hz'
  have hq : Function.Surjective q₀ := ZMod.castHom_surjective _
  have hcomp (x : ZMod a) : q₀ (i₀ x) = 0 := by
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
    rw [hi_cast, map_mul, map_natCast, map_intCast, ZMod.natCast_self, zero_mul]
  have hexact : Function.Exact i₀ q₀ := by
    intro y
    constructor
    · obtain ⟨z, rfl⟩ := ZMod.intCast_surjective y
      intro hz
      have hd : (r : ℤ) ∣ z := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd z r).mp
        simpa only [map_intCast] using hz
      obtain ⟨w, hw⟩ := hd
      exact ⟨(w : ZMod a), by rw [hi_cast, hw, Int.cast_mul, Int.cast_natCast]⟩
    · rintro ⟨x, rfl⟩
      exact hcomp x
  let i : ULift.{u + 1} (ZMod a) →ₗ[ULift.{u + 1} ℤ]
      ULift.{u + 1} (ZMod (a * r)) :=
    { toFun := fun x ↦ ⟨i₀ x.down⟩
      map_add' := by intro x y; exact ULift.ext (i₀.map_add x.down y.down)
      map_smul' := by intro z x; exact ULift.ext (i₀.map_zsmul z.down x.down) }
  let q : ULift.{u + 1} (ZMod (a * r)) →ₗ[ULift.{u + 1} ℤ]
      ULift.{u + 1} (ZMod r) :=
    { toFun := fun y ↦ ⟨q₀ y.down⟩
      map_add' := by intro x y; exact ULift.ext (q₀.map_add x.down y.down)
      map_smul' := by intro z x; exact ULift.ext (q₀.map_zsmul z.down x.down) }
  have hiq : q.comp i = 0 := by
    ext x
    exact hcomp x.down
  let S := ModuleCat.shortComplexOfCompEqZero i q hiq
  have hS : S.ShortExact := by
    apply ModuleCat.shortComplex_shortExact
    · intro y
      change q y = 0 ↔ ∃ x, i x = y
      constructor
      · intro hy
        obtain ⟨x, hx⟩ := (hexact y.down).mp (congrArg ULift.down hy)
        exact ⟨⟨x⟩, ULift.ext hx⟩
      · rintro ⟨x, rfl⟩
        exact ULift.ext (hcomp x.down)
    · intro x y h
      exact ULift.ext (hi (congrArg ULift.down h))
    · intro y
      obtain ⟨x, hx⟩ := hq y.down
      exact ⟨⟨x⟩, ULift.ext hx⟩
  have hmiddle := hext S hS hind hprime
  rw [pow_succ]
  exact hiso (Iso.refl _) hmiddle

end ModuleCat
