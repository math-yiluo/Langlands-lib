import Langlands.Representation.Archimedean.RealInducedPairResonance
import Langlands.Representation.Archimedean.RealInducedPairGenericSwap

/-!
# Filtrations outside the crossing resonance locus

The arithmetic crossing table is identified with the parameters of the proved
generic exchange map. This gives the adjacent filtration outside the common
integer coset, in particular at unequal imaginary exponents. Above the strict
half-weight-gap threshold, absence of a positive linked index suffices.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairGenericRegion

open RealBlockMultiplier RealInducedPairResonance RealInducedPairLinkedReplacement
open RealInducedPairFrobenius RealInducedPairGenericSwap

/-- The generic exchange predicate uses precisely the four arithmetic crossings. -/
theorem isGenericPair_iff_forall (d e : ComplexCharacterData) :
    IsGenericPair d e ↔
      ∀ i : Fin 4, IsGenericParameter (crossingDifference d e i) (crossingParity d e i) := by
  have h0 : crossingDifference d e 0 = swapParameter d e - 1 := by
    dsimp [crossingDifference, swapParameter]
    ring
  have h1 : crossingDifference d e 1 =
      swapParameter d e - 1 + (d.weight.natAbs : ℂ) := by
    dsimp [crossingDifference, swapParameter]
    ring
  have h2 : crossingDifference d e 2 =
      swapParameter d e - 1 + (e.weight.natAbs : ℂ) := by
    dsimp [crossingDifference, swapParameter]
    ring
  have h3 : crossingDifference d e 3 =
      swapParameter d e - 1 + (d.weight.natAbs : ℂ) + (e.weight.natAbs : ℂ) := by
    dsimp [crossingDifference, swapParameter]
    ring
  constructor
  · intro h i
    fin_cases i
    · change IsGenericParameter (crossingDifference d e 0) (crossingParity d e 0)
      simpa [h0, crossingParity] using h.1
    · change IsGenericParameter (crossingDifference d e 1) (crossingParity d e 1)
      simpa [h1, crossingParity] using h.2.1
    · change IsGenericParameter (crossingDifference d e 2) (crossingParity d e 2)
      simpa [h2, crossingParity] using h.2.2.1
    · change IsGenericParameter (crossingDifference d e 3) (crossingParity d e 3)
      simpa [h3, crossingParity] using h.2.2.2
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [h0, crossingParity] using h 0
    · simpa [h1, crossingParity] using h 1
    · simpa [h2, crossingParity] using h 2
    · simpa [h3, crossingParity] using h 3

/-- Genericity is exactly the absence of the four-crossing resonance. -/
theorem isGenericPair_iff_not_resonant (d e : ComplexCharacterData) :
    IsGenericPair d e ↔ ¬ HasCrossingResonance d e := by
  classical
  rw [isGenericPair_iff_forall, HasCrossingResonance]
  simp only [not_exists, not_not]

/-- Avoiding the common integer coset makes all four crossings generic. -/
theorem isGenericPair_of_not_integer_coset {d e : ComplexCharacterData}
    (h : ¬ ∃ q : ℤ, e.exponent - d.exponent = halfWeightGap d e + (q : ℂ)) :
    IsGenericPair d e :=
  (isGenericPair_iff_not_resonant d e).mpr
    (fun hr => h (gap_eq_halfWeightGap_add_int hr))

/-- Unequal imaginary exponents avoid the common integer coset. -/
theorem isGenericPair_of_im_ne {d e : ComplexCharacterData}
    (h : d.exponent.im ≠ e.exponent.im) : IsGenericPair d e := by
  apply isGenericPair_of_not_integer_coset
  rintro ⟨q, hq⟩
  have him := congrArg Complex.im hq
  simp [halfWeightGap] at him
  exact h (by linarith)

/-- Above the strict threshold, genericity is equivalent to absence of a linked index. -/
theorem isGenericPair_iff_no_linked_above_threshold {d e : ComplexCharacterData}
    (hgap : (halfWeightGap d e).re < e.exponent.re - d.exponent.re) :
    IsGenericPair d e ↔ ∀ k : ℕ, ¬ IsLinkedAt d e k := by
  rw [isGenericPair_iff_not_resonant, resonance_iff_exists_linkedAt hgap, not_exists]

/-- The proved generic exchange gives a filtration outside the common integer coset. -/
theorem filtration_of_not_integer_coset {d e : ComplexCharacterData}
    (h : ¬ ∃ q : ℤ, e.exponent - d.exponent = halfWeightGap d e + (q : ℂ)) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) :=
  filtration (isGenericPair_of_not_integer_coset h)

/-- Unequal imaginary exponents admit the proved generic adjacent filtration. -/
theorem filtration_of_im_ne {d e : ComplexCharacterData}
    (h : d.exponent.im ≠ e.exponent.im) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) :=
  filtration (isGenericPair_of_im_ne h)

/-- Nonlinked pairs above the threshold admit the proved generic adjacent filtration. -/
theorem filtration_of_no_linked_above_threshold {d e : ComplexCharacterData}
    (hgap : (halfWeightGap d e).re < e.exponent.re - d.exponent.re)
    (h : ∀ k : ℕ, ¬ IsLinkedAt d e k) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) :=
  filtration ((isGenericPair_iff_no_linked_above_threshold hgap).mpr h)

end RealInducedPairGenericRegion

/-- The adjacent filtration for nonlinked pairs above the strict half-weight-gap threshold. -/
def RealInducedPairNonlinkedAboveThresholdFiltrationStatement : Prop :=
  ∀ d e : ComplexCharacterData,
    (RealInducedPairResonance.halfWeightGap d e).re < e.exponent.re - d.exponent.re →
    (∀ k : ℕ, ¬ RealInducedPairLinkedReplacement.IsLinkedAt d e k) →
      RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)

theorem realInducedPairNonlinkedAboveThresholdFiltration :
    RealInducedPairNonlinkedAboveThresholdFiltrationStatement :=
  fun _ _ hgap h => RealInducedPairGenericRegion.filtration_of_no_linked_above_threshold hgap h

end Langlands.Archimedean
