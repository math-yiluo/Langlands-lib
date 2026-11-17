import Langlands.Representation.Archimedean.RealInducedPairCrossedReplacement
import Langlands.Representation.Archimedean.RealInducedPairNegativeInnerQuotient

/-! # The actual crossed quotient of the positive-inner mixed source -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairCrossedMiddleQuotient

open RealStandardFiltration RealCharacterPair RealInducedPairAscendingExchange
open RealInducedPairLinkedReplacement RealInducedPairCrossedReplacement

namespace N
export RealInducedPairNegativeInnerQuotient (leftParity middleData middleList quotient
  middleInclusion quotient_exact quotient_surjective)
end N

def leftParity (d : ComplexCharacterData) : Fin 2 :=
  ⟨d.weight.natAbs % 2, Nat.mod_lt _ two_pos⟩

def rightParity (d e : ComplexCharacterData) (k : ℕ) : Fin 2 :=
  ⟨(innerWeight d e k).toNat % 2, Nat.mod_lt _ two_pos⟩

abbrev middleList (d e : ComplexCharacterData) (k : ℕ) : List RealBlock :=
  RealInducedPairDistantParity.innerPiece d e k (leftParity d) (rightParity d e k)

variable {d e : ComplexCharacterData} {k : ℕ}

theorem outer_parity (hH : 0 < innerWeight d e k) :
    Even ((outerWeight d e k : ℤ) - 1 -
      pairParity (P.lo d (leftParity d)) (P.hi e (rightParity d e k))) := by
  have hs := RealInducedPairLinkedIncoming.weight_sum d e k
  have hc := Int.toNat_of_nonneg hH.le
  simp only [pairParity, RealInducedPairQuotientPresentation.lo,
    RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData,
    leftParity, rightParity]
  rw [Int.even_iff]
  omega

theorem crossed_negative (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (hH : 0 < innerWeight d e k) :
    innerWeight (lowerData d e k) (upperData d e k) (crossedIndex d e) < 0 := by
  rw [(outer_inner_weights hd he).2]
  omega

theorem crossed_inner_abs (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (hH : 0 < innerWeight d e k) :
    (innerWeight (lowerData d e k) (upperData d e k) (crossedIndex d e)).natAbs =
      (innerWeight d e k).toNat := by
  rw [(outer_inner_weights hd he).2, Int.natAbs_neg]
  have hc := Int.toNat_of_nonneg hH.le
  have ha : ((innerWeight d e k).natAbs : ℤ) = innerWeight d e k := by
    rw [Int.natCast_natAbs, abs_of_pos hH]
  omega

theorem crossed_leftParity (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (hH : 0 < innerWeight d e k) :
    N.leftParity (lowerData d e k) (upperData d e k) (crossedIndex d e) = leftParity d := by
  apply Fin.ext
  simp only [RealInducedPairNegativeInnerQuotient.leftParity,
    crossed_inner_abs hd he hH, lowerData_weight, Int.natAbs_natCast, leftParity]
  have hw := RealInducedPairMiddleParity.weight_id d e k
  have hc := Int.toNat_of_nonneg hH.le
  omega

theorem middleList_eq (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    N.middleList (lowerData d e k) (upperData d e k) (crossedIndex d e) =
      middleList d e k := by
  have hu :
      P.lo (lowerData d e k)
        (N.leftParity (lowerData d e k) (upperData d e k) (crossedIndex d e)) =
      P.lo d (leftParity d) := by
    apply congrArg₂ RealJacquetFrobenius.charData (crossed_leftParity hd he hH)
    exact (lower_endpoints h (leftParity d) (rightParity d e k)
      (N.leftParity (lowerData d e k) (upperData d e k) (crossedIndex d e))).1
  have hy : P.hi (upperData d e k) 0 = P.hi e (rightParity d e k) := by
    apply congrArg₂ RealJacquetFrobenius.charData
    · apply Fin.ext
      simp only [upperData_weight, Int.natAbs_natCast, Fin.val_zero, zero_add,
        rightParity]
      have hw := RealInducedPairMiddleParity.weight_id d e k
      have hc := Int.toNat_of_nonneg hH.le
      omega
    · exact (upper_endpoints h (leftParity d) (rightParity d e k) 0).2
  have hD : N.middleData (lowerData d e k) (upperData d e k) (crossedIndex d e) =
      pairInduced (P.hi d (leftParity d)) (P.lo e (rightParity d e k))
        (innerWeight d e k).toNat := by
    unfold RealInducedPairNegativeInnerQuotient.middleData
    rw [crossed_inner_abs hd he hH]
    unfold pairInduced
    rw [(upper_endpoints h (leftParity d) (rightParity d e k) 0).1,
      (lower_endpoints h (leftParity d) (rightParity d e k)
        (N.leftParity (lowerData d e k) (upperData d e k) (crossedIndex d e))).2]
  change [RealBlock.character _, RealBlock.induced _, RealBlock.character _] =
    [RealBlock.character _, RealBlock.induced _, RealBlock.character _]
  dsimp only [RealInducedPairNegativeInnerQuotient.u, RealInducedPairNegativeInnerQuotient.y]
  rw [hu, hD, hy]

/-- The actual negative-inner quotient, transported to the original mixed source. -/
def quotient (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    KF 4 (middleList d e k) →ₗ[ℂ] KF 4 (crossedPair d e k) :=
  (N.quotient (linked hd he) (crossed_negative hd he hH)).comp
    (ofEqMap (congrArg (KF 4) (middleList_eq hd he h hH).symm))

theorem quotient_exact (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    IsRealIntertwinerModulo 4 (middleList d e k) (crossedPair d e k) ⊥
      (quotient hd he h hH) :=
  modulo_comp_bot (N.quotient_exact (linked hd he) (crossed_negative hd he hH))
    (modulo_ofEqMap _)

theorem quotient_surjective (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    Function.Surjective (quotient hd he h hH) :=
  (N.quotient_surjective (linked hd he) (crossed_negative hd he hH)).comp
    (ofEqMap_surjective _)

/-- The same mixed source included into the crossed four-character presentation. -/
def inclusion (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    KF 4 (middleList d e k) →ₗ[ℂ]
      KF 4 (P.X (lowerData d e k) (upperData d e k)
        (N.leftParity (lowerData d e k) (upperData d e k) (crossedIndex d e)) 0) :=
  (N.middleInclusion (linked hd he) (crossed_negative hd he hH)).comp
    (ofEqMap (congrArg (KF 4) (middleList_eq hd he h hH).symm))

theorem quotient_factorization (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    quotient hd he h hH =
      (P.quotientMap (lowerData d e k) (upperData d e k)
        (N.leftParity (lowerData d e k) (upperData d e k) (crossedIndex d e)) 0
        (by simpa using (RealInducedPairMiddleParity.weights_pos d e k).1)
        (by simpa using (RealInducedPairMiddleParity.weights_pos d e k).2)).comp
          (inclusion hd he h hH) := rfl

/-- Its kernel is the pullback of the two concrete crossed binomial images. -/
theorem ker_quotient (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k) :
    LinearMap.ker (quotient hd he h hH) =
      (LinearMap.range (P.qd (lowerData d e k) (upperData d e k)
          (N.leftParity (lowerData d e k) (upperData d e k) (crossedIndex d e)) 0) ⊔
        LinearMap.range (P.qe (lowerData d e k) (upperData d e k)
          (N.leftParity (lowerData d e k) (upperData d e k) (crossedIndex d e)) 0)).comap
            (inclusion hd he h hH) := by
  rw [quotient_factorization, LinearMap.ker_comp,
    RealInducedPairQuotientPresentation.ker_quotient]

end RealInducedPairCrossedMiddleQuotient

open RealStandardFiltration RealInducedPairLinkedReplacement
  RealInducedPairCrossedReplacement RealInducedPairCrossedMiddleQuotient in
/-- The positive-inner mixed source has an exact surjective crossed quotient. -/
def RealInducedPairCrossedMiddleQuotientStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ)
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs)
    (h : IsLinkedAt d e k) (hH : 0 < innerWeight d e k),
    Even ((outerWeight d e k : ℤ) - 1 -
      RealCharacterPair.pairParity
        (RealInducedPairAscendingExchange.P.lo d (leftParity d))
        (RealInducedPairAscendingExchange.P.hi e (rightParity d e k))) ∧
    IsRealIntertwinerModulo 4 (middleList d e k) (crossedPair d e k) ⊥
      (quotient hd he h hH) ∧
    Function.Surjective (quotient hd he h hH)

theorem realInducedPairCrossedMiddleQuotient : RealInducedPairCrossedMiddleQuotientStatement :=
  fun _ _ _ hd he h hH =>
    ⟨RealInducedPairCrossedMiddleQuotient.outer_parity hH,
      RealInducedPairCrossedMiddleQuotient.quotient_exact hd he h hH,
      RealInducedPairCrossedMiddleQuotient.quotient_surjective hd he h hH⟩

end Langlands.Archimedean
