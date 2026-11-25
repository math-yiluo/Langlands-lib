/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtension
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # A uniformizer power divisible by a specified prime power

Source: Serre, Local Fields, Chapter II, Section 2; blueprint integral finite-level
dual classicality, scalar reduction step.
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace Padic

/-- A positive power of the chosen uniformizer is a multiple of a prescribed positive
power of the residual prime.

Source: Serre, Local Fields, Chapter II, Section 2
(blueprint: lem-sfb-finite-level-uniformizer-multiple).

Proof: the prime has absolute value less than one, and so is a nonunit in the
valuation ring. It is nonzero since its image in the coefficient field is nonzero.
Factor it as a unit times a positive uniformizer power. Raise this factorization
to the requested power and multiply by the inverse of the unit power.
-/
theorem exists_uniformizer_power_multiple
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ a : coefficientExtensionIntegers l E,
      coefficientExtensionUniformizer l E ^ n = (l ^ r) * a := by
  let R := coefficientExtensionIntegers l E
  let π := coefficientExtensionUniformizer l E
  have h := (coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsLocalRing R := h.2.2.2.1
  let : IsDiscreteValuationRing R := h.2.2.2.2.2.2.2.1
  have hπ : Ideal.span ({π} : Set R) = IsLocalRing.maximalIdeal R :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec.trans
      (IsLocalRing.eq_maximalIdeal (R := R) h.2.2.2.2.1)
  have hπi : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ.symm
  have hlE : (l : E) ≠ 0 := by
    rw [← map_natCast (algebraMap (Padic l) E) l]
    exact (map_ne_zero (algebraMap (Padic l) E)).mpr
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  have hlR : (l : R) ≠ 0 := fun hz ↦ hlE (congrArg Subtype.val hz)
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hlR hπi
  have he : 0 < e := by
    by_contra hnot
    have he0 : e = 0 := by omega
    have hunit : IsUnit (l : R) := by simpa only [hv, he0, pow_zero, mul_one] using v.isUnit
    have habs : coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
      change spectralNorm (Padic l) E (l : E) < 1
      rw [← map_natCast (algebraMap (Padic l) E) l, spectralNorm_extends]
      exact Padic.norm_p_lt_one
    exact habs.ne ((h.2.2.1 (l : R)).mp hunit)
  refine ⟨e * r, Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.mul_pos he (by omega))), ((v⁻¹ : Rˣ) : R) ^ r, ?_⟩
  rw [hv, mul_pow, pow_mul]
  simp only [mul_comm ((v : R) ^ r), mul_assoc, ← mul_pow, Units.mul_inv,
    mul_one]
  rfl

end Padic
