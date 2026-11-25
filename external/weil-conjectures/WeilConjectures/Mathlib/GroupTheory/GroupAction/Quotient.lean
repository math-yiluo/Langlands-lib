/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Equivariant maps out of free actions lift along surjections

Let a group `H` act freely on a type `Y`. An `H`-equivariant map `s : Y → N` lifts along any
surjective `H`-equivariant map `π : M → N`: choose a representative of every orbit of `Y` and a
lift of its image, and extend equivariantly, which is well defined as the action is free.

## Main statements

- `MulAction.exists_equivariant_lift_of_free`.
-/

@[expose] public section

namespace MulAction

/-- Let a group `H` act freely on `Y`, and act on `M` and `N` (by functions `aM` and `aN`, with
`aM` multiplicative). An `H`-equivariant map `s : Y → N` lifts along any surjective
`H`-equivariant map `π : M → N` to an `H`-equivariant map `Y → M`. -/
theorem exists_equivariant_lift_of_free {H Y M N : Type*} [Group H] [MulAction H Y]
    (hfree : ∀ (h : H) (y : Y), h • y = y → h = 1) (aM : H → M → M)
    (haM : ∀ g h m, aM (g * h) m = aM g (aM h m)) (aN : H → N → N) (π : M → N)
    (hπ : Function.Surjective π) (hπa : ∀ h m, π (aM h m) = aN h (π m)) (s : Y → N)
    (hs : ∀ h y, s (h • y) = aN h (s y)) :
    ∃ s' : Y → M, (∀ h y, s' (h • y) = aM h (s' y)) ∧ ∀ y, π (s' y) = s y := by
  classical
  let rep (y : Y) : Y := (Quotient.mk (orbitRel H Y) y).out
  have hrep (y : Y) : ∃ h : H, h • rep y = y := by
    have : orbitRel H Y (rep y) y := Quotient.exact (Quotient.out_eq _)
    obtain ⟨h, hh⟩ := (orbitRel_apply.1 this : rep y ∈ orbit H y)
    exact ⟨h⁻¹, by rw [← hh, inv_smul_smul]⟩
  choose c hc using hrep
  choose m hm using hπ
  have hrep_smul (g : H) (y : Y) : rep (g • y) = rep y := by
    refine congrArg Quotient.out (Quotient.sound ?_)
    exact orbitRel_apply.2 ⟨g, rfl⟩
  have hc_smul (g : H) (y : Y) : c (g • y) = g * c y := by
    have h₁ : (c (g • y))⁻¹ * (g * c y) = 1 := by
      refine hfree _ (rep y) ?_
      rw [mul_smul, mul_smul, hc, ← hrep_smul g y, inv_smul_eq_iff, hc]
    exact (inv_mul_eq_one.mp h₁)
  refine ⟨fun y ↦ aM (c y) (m (s (rep y))), fun g y ↦ ?_, fun y ↦ ?_⟩
  · simp only
    rw [hc_smul, hrep_smul, haM]
  · simp only
    rw [hπa, hm, ← hs, hc]

end MulAction
