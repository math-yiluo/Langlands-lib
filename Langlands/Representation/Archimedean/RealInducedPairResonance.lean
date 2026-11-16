import Langlands.Representation.Archimedean.RealInducedPairLinkedReplacement
import Langlands.Representation.Archimedean.RealBlockMultiplierGeneric
import Langlands.Representation.Archimedean.RealBlockPositionData

/-!
# Crossing resonance and the positive linked-gap threshold

The four character-crossing differences lie in a common integer coset. A resonance
above the half-weight-gap threshold therefore gives a positive linked-gap index.
These are arithmetic statements, with no assertion about kernels or occurrence.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.RealInducedPairResonance

open Langlands.LocalFactor.Archimedean
open RealBlockMultiplier RealInducedPairLinkedReplacement

/-- Half the difference of the maximum and minimum absolute weights. -/
def halfWeightGap (d e : ComplexCharacterData) : ℂ :=
  (((max d.weight.natAbs e.weight.natAbs : ℕ) : ℂ) -
    ((min d.weight.natAbs e.weight.natAbs : ℕ) : ℂ)) / 2

/-- The four unshifted character differences, in first/left/right/last order. -/
def crossingDifference (d e : ComplexCharacterData) : Fin 4 → ℂ :=
  ![d.exponent - e.exponent - ((d.weight.natAbs : ℂ) + e.weight.natAbs) / 2,
    d.exponent - e.exponent + ((d.weight.natAbs : ℂ) - e.weight.natAbs) / 2,
    d.exponent - e.exponent + ((e.weight.natAbs : ℂ) - d.weight.natAbs) / 2,
    d.exponent - e.exponent + ((d.weight.natAbs : ℂ) + e.weight.natAbs) / 2]

/-- Reduced parity representatives for the same four crossings. -/
def crossingParity (d e : ComplexCharacterData) : Fin 4 → ℤ :=
  ![((e.weight.natAbs + 1) % 2 : ℕ),
    ((d.weight.natAbs + e.weight.natAbs + 2) % 2 : ℕ),
    0, ((d.weight.natAbs + 1) % 2 : ℕ)]

/-- Original diagonal positions of the two characters exchanged at each crossing. -/
def crossingPositions : Fin 4 → ℕ × ℕ := ![(1, 2), (0, 2), (1, 3), (0, 3)]

/-- Integer offsets from the common half-weight-gap coset. -/
def crossingOffset (d e : ComplexCharacterData) : Fin 4 → ℤ :=
  ![-(max d.weight.natAbs e.weight.natAbs : ℕ),
    (d.weight.natAbs : ℤ) - (max d.weight.natAbs e.weight.natAbs : ℕ),
    (e.weight.natAbs : ℤ) - (max d.weight.natAbs e.weight.natAbs : ℕ),
    (min d.weight.natAbs e.weight.natAbs : ℕ)]

/-- At least one crossing meets its rank-one singular set. -/
def HasCrossingResonance (d e : ComplexCharacterData) : Prop :=
  ∃ i : Fin 4, ¬ IsGenericParameter (crossingDifference d e i) (crossingParity d e i)

/-- The differences are those of the original position characters which cross. -/
theorem crossingDifference_eq_position (d e : ComplexCharacterData) (i : Fin 4) :
    crossingDifference d e i =
      GramFormula.realPositionExponent [.induced d, .induced e] (crossingPositions i).1 -
        GramFormula.realPositionExponent [.induced d, .induced e] (crossingPositions i).2 := by
  fin_cases i <;>
    dsimp [crossingDifference, crossingPositions, GramFormula.realPositionExponent] <;> ring

/-- Each reduced parity is the sum of the signs of the two crossing characters modulo two. -/
theorem crossingParity_eq_position (d e : ComplexCharacterData) (i : Fin 4) :
    crossingParity d e i =
      (((RealBlockPosition.realPositionSign [.induced d, .induced e]
          (crossingPositions i).1).val +
        (RealBlockPosition.realPositionSign [.induced d, .induced e]
          (crossingPositions i).2).val) % 2 : ℕ) := by
  fin_cases i <;>
    dsimp [crossingParity, crossingPositions, RealBlockPosition.realPositionSign] <;>
    apply congrArg (fun n : ℕ => (n : ℤ)) <;>
    norm_num only <;>
    simp only [zero_add, Nat.mod_mod]
  rw [← Nat.add_mod]
  congr 1
  ring

/-- All four differences are in the same integer coset of minus the exponent gap. -/
theorem crossingDifference_eq (d e : ComplexCharacterData) (i : Fin 4) :
    crossingDifference d e i =
      halfWeightGap d e - (e.exponent - d.exponent) + (crossingOffset d e i : ℂ) := by
  have hm : ((max d.weight.natAbs e.weight.natAbs : ℕ) : ℂ) +
      ((min d.weight.natAbs e.weight.natAbs : ℕ) : ℂ) =
      (d.weight.natAbs : ℂ) + (e.weight.natAbs : ℂ) := by
    exact_mod_cast max_add_min d.weight.natAbs e.weight.natAbs
  fin_cases i <;> dsimp [crossingDifference, crossingOffset, halfWeightGap] <;>
    simp only [Int.cast_neg, Int.cast_sub, Int.cast_natCast]
  · linear_combination hm / 2
  · linear_combination hm / 2
  · linear_combination hm / 2
  · linear_combination -hm / 2

private theorem exists_int_of_not_generic {ν : ℂ} {ε : ℤ}
    (h : ¬ IsGenericParameter ν ε) : ∃ q : ℤ, ν = (q : ℂ) := by
  classical
  simp only [IsGenericParameter, not_and_or, not_forall, not_not] at h
  rcases h with ⟨m, hm⟩ | ⟨m, hm⟩
  · refine ⟨ε + 2 * (m : ℤ) + 1, ?_⟩
    simpa using hm
  · refine ⟨-(ε + 2 * (m : ℤ) + 1), ?_⟩
    simpa using hm

/-- Resonance puts the exponent gap in the half-weight-gap integer coset. -/
theorem gap_eq_halfWeightGap_add_int {d e : ComplexCharacterData}
    (h : HasCrossingResonance d e) :
    ∃ q : ℤ, e.exponent - d.exponent = halfWeightGap d e + (q : ℂ) := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨r, hr⟩ := exists_int_of_not_generic hi
  refine ⟨crossingOffset d e i - r, ?_⟩
  have hc := crossingDifference_eq d e i
  push_cast
  linear_combination hc - hr

/-- Above the threshold, the integer coset index is positive and yields a linked index. -/
theorem exists_linkedAt_of_resonance {d e : ComplexCharacterData}
    (h : HasCrossingResonance d e)
    (hgap : (halfWeightGap d e).re < e.exponent.re - d.exponent.re) :
    ∃ k : ℕ, IsLinkedAt d e k := by
  obtain ⟨q, hq⟩ := gap_eq_halfWeightGap_add_int h
  have hqr : e.exponent.re - d.exponent.re = (halfWeightGap d e).re + (q : ℝ) := by
    simpa using congrArg Complex.re hq
  have hqpos : 0 < q := by
    have : (0 : ℝ) < q := by linarith
    exact_mod_cast this
  refine ⟨(q - 1).toNat, (linkedAt_iff _ _ _).mpr ?_⟩
  have hcast : (((q - 1).toNat : ℕ) : ℤ) = q - 1 := Int.toNat_of_nonneg (by omega)
  have hc : (((q - 1).toNat : ℕ) : ℂ) = (q : ℂ) - 1 := by
    simpa using congrArg (fun z : ℤ => (z : ℂ)) hcast
  change e.exponent - d.exponent = halfWeightGap d e + _ + 1
  rw [hc, hq]
  ring

/-- At a linked gap, each crossing difference is its integer offset minus `k+1`. -/
theorem crossingDifference_of_linked {d e : ComplexCharacterData} {k : ℕ}
    (h : IsLinkedAt d e k) (i : Fin 4) :
    crossingDifference d e i = (crossingOffset d e i : ℂ) - (k : ℂ) - 1 := by
  have hg : e.exponent - d.exponent = halfWeightGap d e + (k : ℂ) + 1 :=
    (linkedAt_iff _ _ _).mp h
  rw [crossingDifference_eq, hg]
  ring

private theorem not_generic_neg_nat {r ε : ℕ} (hr : 0 < r) (hε : ε < 2)
    (hp : r % 2 = (ε + 1) % 2) :
    ¬ IsGenericParameter (-(r : ℂ)) (ε : ℤ) := by
  have heq : r = ε + 2 * ((r - ε - 1) / 2) + 1 := by omega
  intro h
  apply h.2 ((r - ε - 1) / 2)
  have hc : (r : ℂ) = (ε : ℂ) + 2 * (((r - ε - 1) / 2 : ℕ) : ℂ) + 1 := by
    exact_mod_cast heq
  simpa only [Int.cast_natCast] using congrArg Neg.neg hc

/-- Every positive linked gap makes at least one of the four crossings resonant. -/
theorem hasCrossingResonance_of_linked {d e : ComplexCharacterData} {k : ℕ}
    (h : IsLinkedAt d e k) : HasCrossingResonance d e := by
  by_cases hLM : d.weight.natAbs ≤ e.weight.natAbs
  · by_cases hk : k % 2 = 0
    · refine ⟨2, ?_⟩
      have heq : crossingDifference d e 2 = -((k + 1 : ℕ) : ℂ) := by
        rw [crossingDifference_of_linked h]
        dsimp [crossingOffset]
        rw [max_eq_right hLM, sub_self]
        simp only [Int.cast_zero, Nat.cast_add, Nat.cast_one]
        ring
      change ¬ IsGenericParameter (crossingDifference d e 2) 0
      rw [heq]
      exact not_generic_neg_nat (by omega) (by norm_num) (by simp [Nat.add_mod, hk])
    · refine ⟨0, ?_⟩
      have heq : crossingDifference d e 0 =
          -((e.weight.natAbs + k + 1 : ℕ) : ℂ) := by
        rw [crossingDifference_of_linked h]
        simp only [crossingOffset, Matrix.cons_val_zero, max_eq_right hLM,
          Int.cast_neg, Int.cast_natCast, Nat.cast_add, Nat.cast_one]
        ring
      rw [heq]
      exact not_generic_neg_nat (by omega) (Nat.mod_lt _ two_pos) (by omega)
  · have hML : e.weight.natAbs ≤ d.weight.natAbs := by omega
    by_cases hk : k % 2 = (d.weight.natAbs + e.weight.natAbs + 2) % 2
    · refine ⟨1, ?_⟩
      have heq : crossingDifference d e 1 = -((k + 1 : ℕ) : ℂ) := by
        rw [crossingDifference_of_linked h]
        simp only [crossingOffset, Matrix.cons_val_one, Matrix.cons_val_zero,
          max_eq_left hML, sub_self, Int.cast_zero, zero_sub, Nat.cast_add, Nat.cast_one]
        ring
      rw [heq]
      exact not_generic_neg_nat (by omega) (Nat.mod_lt _ two_pos) (by omega)
    · refine ⟨0, ?_⟩
      have heq : crossingDifference d e 0 =
          -((d.weight.natAbs + k + 1 : ℕ) : ℂ) := by
        rw [crossingDifference_of_linked h]
        simp only [crossingOffset, Matrix.cons_val_zero, max_eq_left hML,
          Int.cast_neg, Int.cast_natCast, Nat.cast_add, Nat.cast_one]
        ring
      rw [heq]
      exact not_generic_neg_nat (by omega) (Nat.mod_lt _ two_pos) (by omega)

/-- Above the half-weight-gap threshold, resonance is exactly positive linkedness. -/
theorem resonance_iff_exists_linkedAt {d e : ComplexCharacterData}
    (hgap : (halfWeightGap d e).re < e.exponent.re - d.exponent.re) :
    HasCrossingResonance d e ↔ ∃ k : ℕ, IsLinkedAt d e k :=
  ⟨fun h => exists_linkedAt_of_resonance h hgap,
    fun ⟨_, h⟩ => hasCrossingResonance_of_linked h⟩

/-- The arithmetic bridge supplies an allowed heavier list in arbitrary context. -/
theorem exists_heavier_piece_of_resonance (pre post : List RealBlock)
    {d e : ComplexCharacterData} (h : HasCrossingResonance d e)
    (hgap : (halfWeightGap d e).re < e.exponent.re - d.exponent.re) :
    ∃ k : ℕ, IsLinkedAt d e k ∧
      (realExponentSupport (replacementPair d e k)).Perm
        (realExponentSupport [.induced d, .induced e]) ∧
      realWeightSquareSum [.induced d, .induced e] <
        realWeightSquareSum (replacementPair d e k) ∧
      RealStandardFiltration.IsAdjacentPiece pre post (.induced d) (.induced e)
        (pre ++ replacementPair d e k ++ post) := by
  obtain ⟨k, hk⟩ := exists_linkedAt_of_resonance h hgap
  exact ⟨k, hk, support_perm hk, weightSquareSum_lt d e k, isAdjacentPiece pre post hk⟩

/-- A positive gap can be resonant while staying below the linked-gap threshold. -/
theorem resonance_below_threshold :
    HasCrossingResonance (characterOfParams 6 0) (characterOfParams 1 (1 / 2)) ∧
      (characterOfParams 6 0).exponent.re <
        (characterOfParams 1 (1 / 2)).exponent.re ∧
      (characterOfParams 1 (1 / 2)).exponent.re -
          (characterOfParams 6 0).exponent.re <
        (halfWeightGap (characterOfParams 6 0) (characterOfParams 1 (1 / 2))).re ∧
      ∀ k : ℕ, ¬ IsLinkedAt (characterOfParams 6 0) (characterOfParams 1 (1 / 2)) k := by
  refine ⟨⟨1, ?_⟩, ?_, ?_, ?_⟩
  · intro h
    have hne := h.1 0
    norm_num [crossingDifference, crossingParity, characterOfParams_weight,
      characterOfParams_exponent] at hne
  · norm_num [characterOfParams_exponent]
  · norm_num [halfWeightGap, characterOfParams_weight, characterOfParams_exponent]
  · intro k hk
    have hg := congrArg Complex.re ((linkedAt_iff _ _ _).mp hk)
    norm_num [characterOfParams_weight, characterOfParams_exponent] at hg
    have hkn : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith

end Langlands.Archimedean.RealInducedPairResonance
