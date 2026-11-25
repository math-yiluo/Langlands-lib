module

public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Ramification indices in a tower of discrete valuation rings

For a tower `A → B → C` of extensions of discrete valuation rings the ramification index is
multiplicative,

$$e(C/A) = e(B/A)\, e(C/B),$$

so if `e(B/A) = 1` then `e(C/A) = e(C/B)`.

For a commutative square of prime ideals whose bottom edge has ramification index one, the top
edge has ramification index one if and only if the two vertical ramification indices agree, and
the lower vertical index always divides the upper one. These facts give criteria for a weak
solution of `IsDiscreteValuationRing.IntegralClosureBaseChange` to remain a weak solution after
enlarging the field.

## Main results

* `Stacks.DiscreteValuationRing.Ramification.addVal_algebraMap_eq_mul`: the valuation of the image
  of an element scales by the ramification index.
* `Stacks.DiscreteValuationRing.Ramification.ramificationIdx_trans`: multiplicativity in a tower.
* `Stacks.DiscreteValuationRing.Ramification.ramificationIdx_eq_of_isWeaklyUnramified`: if
  `e(B/A) = 1` then `e(C/A) = e(C/B)`.
* `Stacks.DiscreteValuationRing.Ramification.isWeaklyUnramified_of_isWeaklyUnramified`: if
  `e(C/A) = 1` then `e(B/A) = 1` and `e(C/B) = 1`.
* `Stacks.DiscreteValuationRing.Ramification.ramificationIdx_eq_of_mul_eq_of_le`: if
  `e(C/A) = d₁ d₂`, `e(B/A) ≤ d₁` and `e(C/B) ≤ d₂`, then `e(B/A) = d₁` and `e(C/B) = d₂`.
* `Ideal.ramificationIdx_eq_one_of_finiteEtale_square`: ramification index one is preserved by a
  finite étale square.
* `Ideal.ramificationIdx_eq_one_iff_ramificationIdx_vertical_eq`: given ramification index one on
  the bottom edge of a square, the top edge has ramification index one if and only if the two
  vertical ramification indices agree.
* `Ideal.ramificationIdx_vertical_dvd_of_ramificationIdx_eq_one`: given ramification index one on
  the bottom edge, the lower vertical index divides the upper one.
* `Ideal.ramificationIdx_eq_one_iff_ramificationIdx_vertical_le`: given ramification index one on
  the bottom edge, the top edge has ramification index one if and only if the upper vertical index
  is at most the lower one.

In the namespace `IsDiscreteValuationRing.IntegralClosureBaseChange`:

* `IsWeakSolution.of_finiteEtale_square`: a weak solution remains one after a finite étale square.
* `IsWeakSolution.of_ramificationIdx_vertical_eq`: a weak solution remains one when the vertical
  ramification indices agree.
* `IsWeakSolution.of_ramificationIdx_vertical_le`: a weak solution remains one when the upper
  vertical ramification index is at most the lower one.

## References

* [The Stacks Project, Tag 09E6](https://stacks.math.columbia.edu/tag/09E6)
* [The Stacks Project, Tag 09ES](https://stacks.math.columbia.edu/tag/09ES)
-/

@[expose] public section

namespace Stacks.DiscreteValuationRing.Ramification

open IsDiscreteValuationRing

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [FaithfulSMul A B]

/-- The `B`-valuation of the image of an element of `A` is its `A`-valuation scaled by the
ramification index. -/
theorem addVal_algebraMap_eq_mul {a : A} {n : ℕ} (h : addVal A a = (n : ℕ∞)) :
    addVal B (algebraMap A B a) = ((ramificationIdx A B * n : ℕ) : ℕ∞) := by
  obtain ⟨πA, hπAprime⟩ := exists_prime A
  have hπA : Irreducible πA := hπAprime.irreducible
  have ha : a ≠ 0 := by
    rintro rfl
    rw [addVal_zero] at h
    exact (ENat.natCast_ne_top n) h.symm
  obtain ⟨k, u, hk⟩ := eq_unit_mul_pow_irreducible ha hπA
  have hkn : k = n := by exact_mod_cast (addVal_def a u hπA k hk).symm.trans h
  obtain ⟨w, hw⟩ := (u.isUnit).map (algebraMap A B)
  rw [hk, map_mul, map_pow, addVal_mul, addVal_pow, ← hw, addVal_eq_zero_of_unit,
    addVal_algebraMap_eq_ramificationIdx A B πA hπA, hkn]
  push_cast
  simp [nsmul_eq_mul, mul_comm]

variable (C : Type*) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra B C]
  [Algebra A C] [IsScalarTower A B C] [FaithfulSMul B C] [FaithfulSMul A C]

/-- **Ramification indices are multiplicative in a tower**: `e(C/A) = e(B/A) * e(C/B)`. -/
theorem ramificationIdx_trans :
    ramificationIdx A C = ramificationIdx A B * ramificationIdx B C := by
  obtain ⟨πA, hπAprime⟩ := exists_prime A
  have hπA : Irreducible πA := hπAprime.irreducible
  have hAB : addVal B (algebraMap A B πA) = (ramificationIdx A B : ℕ∞) :=
    addVal_algebraMap_eq_ramificationIdx A B πA hπA
  have hBC : addVal C (algebraMap B C (algebraMap A B πA))
      = ((ramificationIdx B C * ramificationIdx A B : ℕ) : ℕ∞) :=
    addVal_algebraMap_eq_mul B C hAB
  have hAC : addVal C (algebraMap A C πA) = (ramificationIdx A C : ℕ∞) :=
    addVal_algebraMap_eq_ramificationIdx A C πA hπA
  rw [IsScalarTower.algebraMap_apply A B C, hBC] at hAC
  rw [mul_comm]
  exact_mod_cast hAC.symm

/-- If `C` has ramification index one over `A`, then `B` has ramification index one over `A` and
`C` has ramification index one over `B`. -/
theorem isWeaklyUnramified_of_isWeaklyUnramified (h : ramificationIdx A C = 1) :
    ramificationIdx A B = 1 ∧ ramificationIdx B C = 1 := by
  rw [ramificationIdx_trans A B C] at h
  exact ⟨Nat.eq_one_of_mul_eq_one_right h,
    Nat.eq_one_of_mul_eq_one_right (by rwa [Nat.mul_comm] at h)⟩

end Stacks.DiscreteValuationRing.Ramification

namespace Ideal

end Ideal

namespace IsDiscreteValuationRing.IntegralClosureBaseChange

attribute [local instance]
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁B₁

end IsDiscreteValuationRing.IntegralClosureBaseChange
