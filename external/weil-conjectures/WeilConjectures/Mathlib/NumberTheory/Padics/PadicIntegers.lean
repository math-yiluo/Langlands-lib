/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Transcendental `p`-adic integers and `ℓ`-adic numbers as fractions

## Main statements

- `PadicInt.exists_transcendental`: there is a `p`-adic integer which is transcendental over `ℤ`.
- `Padic.exists_eq_inv_pow_mul`: every `ℓ`-adic number is of the form `ℓ ^ (-b) * z` with `z` an
  `ℓ`-adic integer, that is, `ℚ_[ℓ] = ℤ_[ℓ][1/ℓ]`.
-/

@[expose] public section

open Cardinal

namespace PadicInt

variable (p : ℕ) [Fact p.Prime]

/-- There is a `p`-adic integer which is transcendental over `ℤ`: otherwise `ℤ_[p]`, and hence
its fraction field `ℚ_[p]`, would be countable, whereas `ℚ_[p]` has the cardinality of the
continuum. -/
theorem exists_transcendental : ∃ t : ℤ_[p], Transcendental ℤ t := by
  by_contra! h
  have : Algebra.IsAlgebraic ℤ ℤ_[p] := ⟨fun t ↦ not_not.mp (h t)⟩
  have hZ : #ℤ_[p] ≤ ℵ₀ := (Algebra.IsAlgebraic.cardinalMk_le_max ℤ ℤ_[p]).trans (by simp)
  have hQ : #ℚ_[p] ≤ ℵ₀ := by
    refine (mk_le_of_surjective (f := fun x : ℤ_[p] × ℤ_[p] ↦ (x.1 : ℚ_[p]) / x.2) ?_).trans ?_
    · intro z
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) z
      exact ⟨(a, b), rfl⟩
    · simpa using mul_le_mul' hZ hZ
  exact (aleph0_lt_continuum.trans_le
    (continuum_le_cardinal_of_nontriviallyNormedField ℚ_[p])).not_ge hQ

end PadicInt

namespace Padic

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- Every `ℓ`-adic number is of the form `ℓ ^ (-b) * z` with `z` an `ℓ`-adic integer, that is,
`ℚ_[ℓ] = ℤ_[ℓ][1/ℓ]`. -/
theorem exists_eq_inv_pow_mul (q : ℚ_[ℓ]) :
    ∃ (b : ℕ) (z : ℤ_[ℓ]), q = ((ℓ : ℚ_[ℓ]) ^ b)⁻¹ * z := by
  obtain ⟨⟨z, d⟩, hzd⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[ℓ]) q
  have hd : (d : ℤ_[ℓ]) ≠ 0 := nonZeroDivisors.ne_zero d.2
  have hspec := PadicInt.unitCoeff_spec hd
  set u := PadicInt.unitCoeff hd
  refine ⟨(d : ℤ_[ℓ]).valuation, z * ↑u⁻¹, ?_⟩
  generalize (d : ℤ_[ℓ]).valuation = v at hspec ⊢
  have hℓ : (ℓ : ℚ_[ℓ]) ^ v ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne ℓ))
  have hu : ((u : ℤ_[ℓ]) : ℚ_[ℓ]) * ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1 := by
    rw [← PadicInt.coe_mul, Units.mul_inv, PadicInt.coe_one]
  simp only [PadicInt.algebraMap_apply] at hzd
  rw [PadicInt.coe_mul, ← hzd, hspec, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
  calc q = q * (((u : ℤ_[ℓ]) : ℚ_[ℓ]) * ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) *
      ((ℓ : ℚ_[ℓ]) ^ v * ((ℓ : ℚ_[ℓ]) ^ v)⁻¹) := by
        rw [hu, mul_inv_cancel₀ hℓ, mul_one, mul_one]
    _ = _ := by ring

end Padic
