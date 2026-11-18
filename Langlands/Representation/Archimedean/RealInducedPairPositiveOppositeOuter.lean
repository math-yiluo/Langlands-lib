import Langlands.Representation.Archimedean.RealInducedPairCrossedMiddleQuotient
import Langlands.Representation.Archimedean.RealInducedPairNegativeOuterKernel

/-! # The opposite outer parity in the positive crossed comparison -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairPositiveOppositeOuter

open RealStandardFiltration RealCharacterPair RealInducedPairAscendingExchange
open RealInducedPairLinkedReplacement RealInducedPairCrossedReplacement

namespace M
export RealInducedPairCrossedMiddleQuotient (leftParity rightParity crossed_negative
  crossed_leftParity crossed_inner_abs)
end M

namespace N
export RealInducedPairNegativeInnerQuotient (leftParity u v x y)
end N

namespace O
export RealInducedPairNegativeOuterQuotient (rawOuter source replacementQuotient)
end O

def flipParity (s : Fin 2) : Fin 2 :=
  ⟨(s.val + 1) % 2, Nat.mod_lt _ two_pos⟩

@[simp] theorem flipParity_flip (s : Fin 2) : flipParity (flipParity s) = s := by
  apply Fin.ext
  have hs := s.isLt
  dsimp [flipParity]
  omega

abbrev oppositeOuter (d e : ComplexCharacterData) (k : ℕ) : List RealBlock :=
  RealInducedPairDistantParity.outerPiece d e k
    (flipParity (M.leftParity d)) (flipParity (M.rightParity d e k))

abbrev crossedCompanion (d e : ComplexCharacterData) (k : ℕ) : List RealBlock :=
  [.character (N.v (lowerData d e k) (upperData d e k) (crossedIndex d e)),
    .induced (O.rawOuter (lowerData d e k) (upperData d e k) (crossedIndex d e)),
    .character (N.x (upperData d e k))]

variable {d e : ComplexCharacterData} {k : ℕ}

theorem crossed_v (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    N.v (lowerData d e k) (upperData d e k) (crossedIndex d e) =
      P.lo e (flipParity (M.rightParity d e k)) := by
  change RealJacquetFrobenius.charData _ _ = RealJacquetFrobenius.charData _ _
  apply congrArg₂ RealJacquetFrobenius.charData
  · apply Fin.ext
    have hp := congrArg Fin.val (M.crossed_leftParity hd he hH)
    have hw := RealInducedPairMiddleParity.weight_id d e k
    have hc := Int.toNat_of_nonneg hH.le
    simp only [lowerData_weight, Int.natAbs_natCast,
      flipParity, RealInducedPairCrossedMiddleQuotient.rightParity,
      RealInducedPairCrossedMiddleQuotient.leftParity] at hp ⊢
    omega
  · exact (lower_endpoints h (flipParity (M.leftParity d))
      (flipParity (M.rightParity d e k))
      (N.leftParity (lowerData d e k) (upperData d e k) (crossedIndex d e))).2

theorem crossed_x (h : IsLinkedAt d e k) :
    N.x (upperData d e k) =
      P.hi d (flipParity (M.leftParity d)) := by
  change RealJacquetFrobenius.charData _ _ = RealJacquetFrobenius.charData _ _
  apply congrArg₂ RealJacquetFrobenius.charData
  · apply Fin.ext
    simp only [flipParity,
      RealInducedPairCrossedMiddleQuotient.leftParity]
    omega
  · exact (upper_endpoints h (flipParity (M.leftParity d))
      (flipParity (M.rightParity d e k)) 0).1

theorem crossed_outer (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) :
    O.rawOuter (lowerData d e k) (upperData d e k) (crossedIndex d e) =
      pairInduced (P.lo d (flipParity (M.leftParity d)))
        (P.hi e (flipParity (M.rightParity d e k))) (outerWeight d e k) := by
  change pairInduced
    (P.lo (lowerData d e k) (N.leftParity (lowerData d e k) (upperData d e k) (crossedIndex d e)))
    (P.hi (upperData d e k) 0) _ = _
  rw [(outer_inner_weights hd he).1]
  unfold pairInduced
  rw [(lower_endpoints h (flipParity (M.leftParity d))
      (flipParity (M.rightParity d e k))
      (N.leftParity (lowerData d e k) (upperData d e k) (crossedIndex d e))).1,
    (upper_endpoints h (flipParity (M.leftParity d))
      (flipParity (M.rightParity d e k)) 0).2]

theorem crossed_companion_eq_opposite
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    crossedCompanion d e k = oppositeOuter d e k := by
  change [RealBlock.character _, RealBlock.induced _, RealBlock.character _] =
    [RealBlock.character _, RealBlock.induced _, RealBlock.character _]
  rw [crossed_v hd he h hH, crossed_outer hd he h, crossed_x h]

theorem negative_source_eq
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    O.source (lowerData d e k) (upperData d e k) (crossedIndex d e) =
      [.character (P.hi d (flipParity (M.leftParity d))),
        .induced (pairInduced (P.lo d (flipParity (M.leftParity d)))
          (P.hi e (flipParity (M.rightParity d e k))) (outerWeight d e k)),
        .character (P.lo e (flipParity (M.rightParity d e k)))] := by
  change [RealBlock.character (N.x (upperData d e k)),
    RealBlock.induced (O.rawOuter (lowerData d e k) (upperData d e k) (crossedIndex d e)),
    RealBlock.character (N.v (lowerData d e k) (upperData d e k) (crossedIndex d e))] = _
  rw [crossed_x h, crossed_outer hd he h, crossed_v hd he h hH]

theorem opposite_outer_parity (hH : 0 < innerWeight d e k) :
    Even ((outerWeight d e k : ℤ) - 1 -
      pairParity (P.lo d (flipParity (M.leftParity d)))
        (P.hi e (flipParity (M.rightParity d e k)))) := by
  have hp := RealInducedPairCrossedMiddleQuotient.outer_parity hH
  simp only [pairParity, RealInducedPairQuotientPresentation.lo,
    RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData,
    flipParity] at hp ⊢
  rw [Int.even_iff] at hp ⊢
  omega

theorem opposite_allowed (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    IsAdjacentPiece [] [] (.induced d) (.induced e) (oppositeOuter d e k) := by
  refine ⟨oppositeOuter d e k, rfl,
    Or.inr ⟨RealInducedPairDistantParity.outer_support h, ?_⟩⟩
  rw [RealInducedPairDistantParity.outer_weightSquareSum]
  have hs := RealInducedPairLinkedIncoming.weight_sum d e k
  have hP : d.weight.natAbs + e.weight.natAbs < outerWeight d e k := by omega
  simp only [realWeightSquareSum, realBlockWeightSquare, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  exact (pow_add_pow_le (Nat.zero_le _) (Nat.zero_le _) two_ne_zero).trans_lt
    (Nat.pow_lt_pow_left hP two_ne_zero)

abbrev negativeOuter (d e : ComplexCharacterData) (k : ℕ) : List RealBlock :=
  O.source (lowerData d e k) (upperData d e k) (crossedIndex d e)

def negativeQuotient (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (hH : 0 < innerWeight d e k) :=
  O.replacementQuotient (linked hd he) (M.crossed_negative hd he hH)

/-- The opposite positive outer source generates the crossed negative outer quotient kernel. -/
def kernelGenerator (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    KF 4 (oppositeOuter d e k) →ₗ[ℂ] KF 4 (negativeOuter d e k) :=
  (RealInducedPairNegativeOuterKernel.kernelGenerator
    (linked hd he) (M.crossed_negative hd he hH)).comp
      (ofEqMap (congrArg (KF 4) (crossed_companion_eq_opposite hd he h hH).symm))

theorem kernelGenerator_exact (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    IsRealIntertwinerModulo 4 (oppositeOuter d e k) (negativeOuter d e k) ⊥
      (kernelGenerator hd he h hH) :=
  modulo_comp_bot
    (RealInducedPairNegativeOuterKernel.kernelGenerator_exact
      (linked hd he) (M.crossed_negative hd he hH))
    (modulo_ofEqMap _)

theorem range_kernelGenerator (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    LinearMap.range (kernelGenerator hd he h hH) =
      LinearMap.ker (negativeQuotient hd he hH) :=
  (LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr
      (ofEqMap_surjective
        (congrArg (KF 4) (crossed_companion_eq_opposite hd he h hH).symm)))).trans
    (RealInducedPairNegativeOuterKernel.range_kernelGenerator
      (linked hd he) (M.crossed_negative hd he hH))

end RealInducedPairPositiveOppositeOuter

open RealStandardFiltration RealInducedPairLinkedReplacement
  RealInducedPairPositiveOppositeOuter in
/-- The second outer parity is an actual kernel source in the crossed negative comparison. -/
def RealInducedPairPositiveOppositeOuterStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ)
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (_h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k),
    IsAdjacentPiece [] [] (.induced d) (.induced e) (oppositeOuter d e k) ∧
      ∃ K : KF 4 (oppositeOuter d e k) →ₗ[ℂ] KF 4 (negativeOuter d e k),
        IsRealIntertwinerModulo 4 (oppositeOuter d e k) (negativeOuter d e k) ⊥ K ∧
        LinearMap.range K = LinearMap.ker (negativeQuotient hd he hH)

theorem realInducedPairPositiveOppositeOuter : RealInducedPairPositiveOppositeOuterStatement := by
  intro d e k hd he h hH
  exact ⟨RealInducedPairPositiveOppositeOuter.opposite_allowed h hH,
    RealInducedPairPositiveOppositeOuter.kernelGenerator hd he h hH,
    RealInducedPairPositiveOppositeOuter.kernelGenerator_exact hd he h hH,
    RealInducedPairPositiveOppositeOuter.range_kernelGenerator hd he h hH⟩

end Langlands.Archimedean
