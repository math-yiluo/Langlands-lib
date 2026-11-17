import Langlands.Representation.Archimedean.RealInducedPairMiddleParity

/-! # Crossed endpoint replacement of two linked real induction blocks -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairCrossedReplacement

open RealCharacterPair RealInducedPairAscendingExchange
open RealInducedPairLinkedReplacement RealInducedPairMiddleParity

/-- Pair the two lower endpoints, independently of the presentation parities. -/
def lowerData (d e : ComplexCharacterData) (k : ℕ) : ComplexCharacterData :=
  pairInduced (P.lo d 0) (P.lo e 0) (lowerWeight d e k)

/-- Pair the two upper endpoints, independently of the presentation parities. -/
def upperData (d e : ComplexCharacterData) (k : ℕ) : ComplexCharacterData :=
  pairInduced (P.hi d 0) (P.hi e 0) (upperWeight d e k)

def crossedPair (d e : ComplexCharacterData) (k : ℕ) : List RealBlock :=
  [.induced (lowerData d e k), .induced (upperData d e k)]

/-- The linked index of the crossed pair when both original weights are positive. -/
def crossedIndex (d e : ComplexCharacterData) : ℕ :=
  min d.weight.natAbs e.weight.natAbs - 1

@[simp] theorem rank (d e : ComplexCharacterData) (k : ℕ) :
    realRank (crossedPair d e k) = 4 := rfl

@[simp] theorem lowerData_weight (d e : ComplexCharacterData) (k : ℕ) :
    (lowerData d e k).weight = (lowerWeight d e k : ℤ) := rfl

@[simp] theorem upperData_weight (d e : ComplexCharacterData) (k : ℕ) :
    (upperData d e k).weight = (upperWeight d e k : ℤ) := rfl

theorem lowerData_eq (d e : ComplexCharacterData) (k : ℕ) (sd se : Fin 2) :
    lowerData d e k = pairInduced (P.lo d sd) (P.lo e se) (lowerWeight d e k) := rfl

theorem upperData_eq (d e : ComplexCharacterData) (k : ℕ) (sd se : Fin 2) :
    upperData d e k = pairInduced (P.hi d sd) (P.hi e se) (upperWeight d e k) := rfl

variable {d e : ComplexCharacterData} {k : ℕ}

theorem support_eq (h : IsLinkedAt d e k) (sd se : Fin 2) :
    realExponentSupport (crossedPair d e k) =
      [(P.lo e se).exponent, (P.lo d sd).exponent,
        (P.hi e se).exponent, (P.hi d sd).exponent] := by
  change realExponentSupport [.induced (lowerData d e k)] ++
    realExponentSupport [.induced (upperData d e k)] = _
  rw [lowerData_eq d e k sd se, upperData_eq d e k sd se,
    realExponentSupport_pairInduced_eq (lower_difference h),
    realExponentSupport_pairInduced_eq (upper_difference h)]
  rfl

theorem support_perm (h : IsLinkedAt d e k) :
    (realExponentSupport (crossedPair d e k)).Perm
      (realExponentSupport [.induced d, .induced e]) := by
  rw [support_eq h 0 0]
  have hh := lower_support (sd := 0) (se := 0) h
  rwa [lower_support_eq h] at hh

@[simp] theorem weightSquareSum (d e : ComplexCharacterData) (k : ℕ) :
    realWeightSquareSum (crossedPair d e k) =
      lowerWeight d e k ^ 2 + upperWeight d e k ^ 2 := by
  simp [crossedPair, realWeightSquareSum, realBlockWeightSquare]

/-- The exact signed increase is twice the product of the inner and outer weights. -/
theorem weightSquareSum_gap (d e : ComplexCharacterData) (k : ℕ) :
    (realWeightSquareSum (crossedPair d e k) : ℤ) -
      (realWeightSquareSum [.induced d, .induced e] : ℤ) =
        2 * innerWeight d e k * (outerWeight d e k : ℤ) := by
  have hw := weight_id d e k
  have hs := RealInducedPairLinkedIncoming.weight_sum d e k
  rw [weightSquareSum]
  simp only [realWeightSquareSum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, realBlockWeightSquare, add_zero, Nat.cast_add, Nat.cast_pow]
  rw [hw.1, hw.2, ← hs]
  ring

theorem weightSquareSum_lt (hH : 0 < innerWeight d e k) :
    realWeightSquareSum [.induced d, .induced e] <
      realWeightSquareSum (crossedPair d e k) := by
  have hP : 0 < (outerWeight d e k : ℤ) := by
    dsimp [outerWeight]
    positivity
  have hg := weightSquareSum_gap d e k
  have hpos : 0 < 2 * innerWeight d e k * (outerWeight d e k : ℤ) :=
    mul_pos (mul_pos (by norm_num) hH) hP
  exact_mod_cast (show (realWeightSquareSum [.induced d, .induced e] : ℤ) <
    (realWeightSquareSum (crossedPair d e k) : ℤ) by omega)

theorem isAdjacentPiece (pre post : List RealBlock) (h : IsLinkedAt d e k)
    (hH : 0 < innerWeight d e k) :
    RealStandardFiltration.IsAdjacentPiece pre post (.induced d) (.induced e)
      (pre ++ crossedPair d e k ++ post) :=
  ⟨crossedPair d e k, rfl, Or.inr ⟨support_perm h, weightSquareSum_lt hH⟩⟩

theorem center_difference (d e : ComplexCharacterData) (k : ℕ) :
    (upperData d e k).exponent - (lowerData d e k).exponent =
      ((d.weight.natAbs : ℂ) + (e.weight.natAbs : ℂ)) / 2 := by
  simp only [upperData, lowerData, pairInduced_exponent,
    RealInducedPairQuotientPresentation.lo, RealInducedPairQuotientPresentation.hi,
    RealJacquetFrobenius.charData]
  ring

theorem min_max_weights (d e : ComplexCharacterData) (k : ℕ) :
    min (lowerWeight d e k) (upperWeight d e k) = k + 1 ∧
    max (lowerWeight d e k) (upperWeight d e k) =
      max d.weight.natAbs e.weight.natAbs - min d.weight.natAbs e.weight.natAbs + k + 1 := by
  rcases le_total d.weight.natAbs e.weight.natAbs with hh | hh
  · simp only [lowerWeight, upperWeight, outerWeight, max_eq_right hh, min_eq_left hh]
    omega
  · simp only [lowerWeight, upperWeight, outerWeight, max_eq_left hh, min_eq_right hh]
    omega

theorem linked (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) :
    IsLinkedAt (lowerData d e k) (upperData d e k) (crossedIndex d e) := by
  rw [linkedAt_iff, center_difference]
  simp only [lowerData_weight, upperData_weight, Int.natAbs_natCast]
  rw [(min_max_weights d e k).1, (min_max_weights d e k).2]
  have hsum := max_add_min d.weight.natAbs e.weight.natAbs
  have hmin : min d.weight.natAbs e.weight.natAbs ≤ max d.weight.natAbs e.weight.natAbs :=
    min_le_max
  have hidx : crossedIndex d e + 1 = min d.weight.natAbs e.weight.natAbs := by
    dsimp [crossedIndex]
    omega
  have hc : ((max d.weight.natAbs e.weight.natAbs - min d.weight.natAbs e.weight.natAbs
      + k + 1 : ℕ) : ℂ) =
      (d.weight.natAbs : ℂ) + e.weight.natAbs -
        2 * (crossedIndex d e : ℂ) + (k : ℂ) - 1 := by
    have hi : ((max d.weight.natAbs e.weight.natAbs -
        min d.weight.natAbs e.weight.natAbs + k + 1 : ℕ) : ℤ) =
        (d.weight.natAbs : ℤ) + e.weight.natAbs -
          2 * (crossedIndex d e : ℤ) + k - 1 := by omega
    exact_mod_cast hi
  rw [hc]
  push_cast
  ring

theorem outer_inner_weights (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) :
    outerWeight (lowerData d e k) (upperData d e k) (crossedIndex d e) =
        outerWeight d e k ∧
    innerWeight (lowerData d e k) (upperData d e k) (crossedIndex d e) =
        -innerWeight d e k := by
  simp only [outerWeight, innerWeight, lowerData_weight, upperData_weight,
    Int.natAbs_natCast]
  rw [(min_max_weights d e k).1, (min_max_weights d e k).2]
  dsimp [crossedIndex]
  have hm : min d.weight.natAbs e.weight.natAbs ≤ max d.weight.natAbs e.weight.natAbs :=
    min_le_max
  constructor <;> omega

theorem middle_weights (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) :
    lowerWeight (lowerData d e k) (upperData d e k) (crossedIndex d e) =
        d.weight.natAbs ∧
    upperWeight (lowerData d e k) (upperData d e k) (crossedIndex d e) =
        e.weight.natAbs := by
  simp only [lowerWeight, upperWeight, (outer_inner_weights hd he).1,
    lowerData_weight, upperData_weight, Int.natAbs_natCast]
  have hd' := le_max_left d.weight.natAbs e.weight.natAbs
  have he' := le_max_right d.weight.natAbs e.weight.natAbs
  dsimp [lowerWeight, upperWeight, outerWeight]
  constructor <;> omega

theorem pair_endpoints {c c' : RealCharacterData} {ℓ : ℕ}
    (h : c'.exponent - c.exponent = (ℓ : ℂ)) (s : Fin 2) :
    (P.lo (pairInduced c c' ℓ) s).exponent = c.exponent ∧
    (P.hi (pairInduced c c' ℓ) s).exponent = c'.exponent := by
  simp only [RealInducedPairQuotientPresentation.lo, RealInducedPairQuotientPresentation.hi,
    RealJacquetFrobenius.charData, pairInduced_weight, pairInduced_exponent,
    Int.natAbs_natCast]
  rw [← h]
  constructor <;> ring

theorem lower_endpoints (h : IsLinkedAt d e k) (sd se s : Fin 2) :
    (P.lo (lowerData d e k) s).exponent = (P.lo d sd).exponent ∧
    (P.hi (lowerData d e k) s).exponent = (P.lo e se).exponent := by
  rw [lowerData_eq d e k sd se]
  exact pair_endpoints (lower_difference h) s

theorem upper_endpoints (h : IsLinkedAt d e k) (sd se s : Fin 2) :
    (P.lo (upperData d e k) s).exponent = (P.hi d sd).exponent ∧
    (P.hi (upperData d e k) s).exponent = (P.hi e se).exponent := by
  rw [upperData_eq d e k sd se]
  exact pair_endpoints (upper_difference h) s

/-- Repeating the crossed pairing recovers the positive-weight normalization. -/
theorem twice (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) :
    lowerData (lowerData d e k) (upperData d e k) (crossedIndex d e) =
        characterOfParams (d.weight.natAbs : ℤ) d.exponent ∧
    upperData (lowerData d e k) (upperData d e k) (crossedIndex d e) =
        characterOfParams (e.weight.natAbs : ℤ) e.exponent := by
  constructor
  · change pairInduced _ _ _ = _
    rw [(middle_weights hd he).1]
    unfold pairInduced
    rw [(lower_endpoints h 0 0 0).1, (upper_endpoints h 0 0 0).1]
    apply congrArg (characterOfParams (d.weight.natAbs : ℤ))
    simp only [RealInducedPairQuotientPresentation.lo,
      RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData]
    ring
  · change pairInduced _ _ _ = _
    rw [(middle_weights hd he).2]
    unfold pairInduced
    rw [(lower_endpoints h 0 0 0).2, (upper_endpoints h 0 0 0).2]
    apply congrArg (characterOfParams (e.weight.natAbs : ℤ))
    simp only [RealInducedPairQuotientPresentation.lo,
      RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData]
    ring

end RealInducedPairCrossedReplacement

open RealInducedPairCrossedReplacement RealInducedPairLinkedReplacement in
/-- Support, weight increase and the signed-inner involution of the crossed pair. -/
def RealInducedPairCrossedReplacementStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ),
    0 < d.weight.natAbs → 0 < e.weight.natAbs → IsLinkedAt d e k →
      (realExponentSupport (crossedPair d e k)).Perm
        (realExponentSupport [.induced d, .induced e]) ∧
      ((realWeightSquareSum (crossedPair d e k) : ℤ) -
        (realWeightSquareSum [.induced d, .induced e] : ℤ) =
          2 * innerWeight d e k * (outerWeight d e k : ℤ)) ∧
      (0 < innerWeight d e k →
        RealStandardFiltration.IsAdjacentPiece [] [] (.induced d) (.induced e)
          (crossedPair d e k)) ∧
      IsLinkedAt (lowerData d e k) (upperData d e k) (crossedIndex d e) ∧
      outerWeight (lowerData d e k) (upperData d e k) (crossedIndex d e) =
        outerWeight d e k ∧
      innerWeight (lowerData d e k) (upperData d e k) (crossedIndex d e) =
        -innerWeight d e k ∧
      lowerData (lowerData d e k) (upperData d e k) (crossedIndex d e) =
        characterOfParams (d.weight.natAbs : ℤ) d.exponent ∧
      upperData (lowerData d e k) (upperData d e k) (crossedIndex d e) =
        characterOfParams (e.weight.natAbs : ℤ) e.exponent

theorem realInducedPairCrossedReplacement : RealInducedPairCrossedReplacementStatement := by
  intro d e k hd he h
  open RealInducedPairCrossedReplacement in
    exact ⟨support_perm h, weightSquareSum_gap d e k,
      fun hH => by simpa using isAdjacentPiece [] [] h hH,
      linked hd he, (outer_inner_weights hd he).1, (outer_inner_weights hd he).2,
      (twice hd he h).1, (twice hd he h).2⟩

end Langlands.Archimedean
