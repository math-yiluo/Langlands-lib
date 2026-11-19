import Langlands.Representation.Archimedean.RealInducedPairNegativeInnerFiltration
import Langlands.Representation.Archimedean.RealInducedSwapGeneric

/-! # The negative-inner ascending word with even lower left endpoint -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealInducedPairNegativeAscendingWord

open Langlands.LocalFactor.Archimedean RealStandardFiltration RealBlockFrobeniusMap
  RealBlockMultiplier RealCharacterPair RealCharacterPairReducible
  RealInducedPairAscendingExchange RealInducedPairLinkedReplacement
open RealInducedPairNegativeInnerQuotient (cutoff_bounds)

abbrev innerCutoff (d e : ComplexCharacterData) (k : ℕ) := (innerWeight d e k).natAbs
abbrev leftGap (d e : ComplexCharacterData) (k : ℕ) := d.weight.natAbs - innerCutoff d e k
abbrev rightGap (d e : ComplexCharacterData) (k : ℕ) := e.weight.natAbs - innerCutoff d e k

/-- The lower endpoint of the right induction block has the parity of the left gap. -/
abbrev rightParity (d e : ComplexCharacterData) (k : ℕ) : Fin 2 :=
  RealCharacterInducedPushforward.fin2 (leftGap d e k)

abbrev u (d : ComplexCharacterData) := P.lo d 0
abbrev v (d : ComplexCharacterData) := P.hi d 0
abbrev x (d e : ComplexCharacterData) (k : ℕ) := P.lo e (rightParity d e k)
abbrev y (d e : ComplexCharacterData) (k : ℕ) := P.hi e (rightParity d e k)

abbrev outerSource (d e : ComplexCharacterData) (k : ℕ) :=
  RealInducedPairDistantParity.outerPiece d e k 0 (rightParity d e k)

variable {d e : ComplexCharacterData} {k : ℕ}

theorem innerCutoff_cast (hneg : innerWeight d e k < 0) :
    (innerCutoff d e k : ℤ) = -innerWeight d e k := by
  rw [innerCutoff, Int.natCast_natAbs, abs_of_neg hneg]

theorem weight_eq (hneg : innerWeight d e k < 0) :
    outerWeight d e k + innerCutoff d e k = d.weight.natAbs + e.weight.natAbs := by
  have hh := innerCutoff_cast hneg
  have hs := RealInducedPairLinkedIncoming.weight_sum d e k
  omega

theorem gap_bounds (hneg : innerWeight d e k < 0) :
    0 < leftGap d e k ∧ 0 < rightGap d e k := by
  obtain ⟨_, hd, he⟩ := cutoff_bounds hneg
  exact ⟨Nat.sub_pos_of_lt hd, Nat.sub_pos_of_lt he⟩

theorem gaps_add (hneg : innerWeight d e k < 0) :
    leftGap d e k + innerCutoff d e k = d.weight.natAbs ∧
    rightGap d e k + innerCutoff d e k = e.weight.natAbs ∧
    leftGap d e k + e.weight.natAbs = outerWeight d e k ∧
    rightGap d e k + d.weight.natAbs = outerWeight d e k := by
  obtain ⟨_, hd, he⟩ := cutoff_bounds hneg
  change innerCutoff d e k < d.weight.natAbs at hd
  change innerCutoff d e k < e.weight.natAbs at he
  have hw := weight_eq hneg
  unfold leftGap rightGap
  omega

theorem u_parity : (u d).parity = 0 := rfl

theorem v_parity_val : (v d).parity.val = (d.weight.natAbs + 1) % 2 := by
  change (0 + d.weight.natAbs + 1) % 2 = _
  rw [zero_add]

theorem x_parity_val : (x d e k).parity.val = leftGap d e k % 2 := rfl

theorem y_parity_val :
    (y d e k).parity.val = (leftGap d e k % 2 + e.weight.natAbs + 1) % 2 := rfl

theorem outer_parity (hneg : innerWeight d e k < 0) :
    Even ((outerWeight d e k : ℤ) - 1 - pairParity (u d) (y d e k)) := by
  have h := (gaps_add hneg).2.2.1
  simp only [pairParity, u_parity, Fin.val_zero, zero_add, y_parity_val]
  rw [Int.even_iff]
  omega

theorem inner_parity (hneg : innerWeight d e k < 0) :
    Even ((innerCutoff d e k : ℤ) - 1 - pairParity (x d e k) (v d)) := by
  have h := (gaps_add hneg).1
  simp only [pairParity, x_parity_val, v_parity_val]
  rw [Int.even_iff]
  omega

theorem left_parity : Even ((leftGap d e k : ℤ) - pairParity (x d e k) (u d)) := by
  unfold pairParity
  change Even ((leftGap d e k : ℤ) - (((leftGap d e k % 2 + 0) % 2 : ℕ) : ℤ))
  rw [Int.even_iff]
  omega

theorem right_parity (hneg : innerWeight d e k < 0) :
    Even ((rightGap d e k : ℤ) - pairParity (y d e k) (v d)) := by
  obtain ⟨hL, hM, -⟩ := gaps_add hneg
  simp only [pairParity, y_parity_val, v_parity_val]
  rw [Int.even_iff]
  omega

theorem gaps (hlink : IsLinkedAt d e k) (hneg : innerWeight d e k < 0) :
    (y d e k).exponent - (u d).exponent = (outerWeight d e k : ℂ) ∧
    (x d e k).exponent - (u d).exponent = (leftGap d e k : ℂ) ∧
    (y d e k).exponent - (v d).exponent = (rightGap d e k : ℂ) ∧
    (v d).exponent - (x d e k).exponent = (innerCutoff d e k : ℂ) := by
  obtain ⟨hP, hA, hB, hh⟩ :=
    RealInducedPairDistantParity.differences (sd := 0) (se := rightParity d e k) hlink
  have hc : (innerCutoff d e k : ℂ) = -(innerWeight d e k : ℂ) := by
    simpa only [Int.cast_natCast, Int.cast_neg] using
      congrArg (fun q : ℤ => (q : ℂ)) (innerCutoff_cast hneg)
  have hL : (leftGap d e k : ℂ) + (innerCutoff d e k : ℂ) = (d.weight.natAbs : ℂ) := by
    exact_mod_cast (gaps_add hneg).1
  have hM : (rightGap d e k : ℂ) + (innerCutoff d e k : ℂ) = (e.weight.natAbs : ℂ) := by
    exact_mod_cast (gaps_add hneg).2.1
  exact ⟨hP, by linear_combination hA - hL + hc,
    by linear_combination hB - hM + hc, by linear_combination -hh - hc⟩

private theorem genericAt_nat {m : ℕ} {ε : ℤ} (he : ε = 0 ∨ ε = 1)
    (hp : Even ((m : ℤ) - ε)) : IsGenericParameter (m : ℂ) ε := by
  constructor
  · intro i hi
    have heq : (m : ℤ) = ε + 2 * (i : ℤ) + 1 := by exact_mod_cast hi
    rw [Int.even_iff] at hp
    omega
  · intro i hi
    have heq : (m : ℤ) = -(ε + 2 * (i : ℤ) + 1) := by exact_mod_cast hi
    omega

/-- The first binomial in the incoming four-crossing word. -/
abbrev outerMultiplier (d e : ComplexCharacterData) (k : ℕ) :=
  binomialMultiplier (outerWeight d e k) (pairParity (u d) (y d e k))

/-- The normalized generic multiplier for the first middle crossing. -/
abbrev leftMultiplier (d e : ComplexCharacterData) (k : ℕ) :=
  genericMultiplier ((leftGap d e k : ℂ) + 0) (pairParity (x d e k) (u d))

/-- The normalized generic multiplier for the second middle crossing. -/
abbrev rightMultiplier (d e : ComplexCharacterData) (k : ℕ) :=
  genericMultiplier ((rightGap d e k : ℂ) + 0) (pairParity (y d e k) (v d))

/-- The final canonical tail, with the sign of the character swap. -/
abbrev innerMultiplier (d e : ComplexCharacterData) (k : ℕ) :=
  tailMultiplier (innerCutoff d e k) (pairParity (x d e k) (v d))
    ((-1 : ℂ) ^ (pairParity (x d e k) (v d)).natAbs)

theorem left_nonzero {j : ℤ} : leftMultiplier d e k j ≠ 0 := by
  have hg := genericAt_nat (pairParity_eq (x d e k) (u d)) left_parity
  simpa only [leftMultiplier, add_zero] using genericMultiplier_ne_zero_of_ne hg.1 hg.2 j

theorem right_nonzero (hneg : innerWeight d e k < 0) {j : ℤ} : rightMultiplier d e k j ≠ 0 := by
  have hg := genericAt_nat (pairParity_eq (y d e k) (v d)) (right_parity hneg)
  simpa only [rightMultiplier, add_zero] using genericMultiplier_ne_zero_of_ne hg.1 hg.2 j

/-- Recurrent multiplier data for the actual incoming ascending word. -/
theorem incomingData (hlink : IsLinkedAt d e k) (hneg : innerWeight d e k < 0) :
    MultiplierData e d (rightParity d e k) 0 (outerMultiplier d e k)
      (leftMultiplier d e k) (rightMultiplier d e k) (innerMultiplier d e k) := by
  obtain ⟨hP, hA, hB, hh⟩ := gaps hlink hneg
  have hpar0 := pairParity_eq (x d e k) (u d)
  have hpar2 := pairParity_eq (y d e k) (v d)
  have hg0 := genericAt_nat hpar0 left_parity
  have hg2 := genericAt_nat hpar2 (right_parity hneg)
  have hcomm := RealInducedSwapGeneric.pairParity_comm
  have hi := isRecurrent_tailMultiplier (cutoff_bounds hneg).1
    (pairParity_eq (x d e k) (v d)) (inner_parity hneg)
    (neg_one_pow_sq (pairParity (x d e k) (v d)).natAbs)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isSymmetric_binomialMultiplier _ (pairParity_eq _ _)
  · change IsSymmetric (pairParity (u d) (x d e k)) (sigma0 (u d) (x d e k)) _
    rw [sigma0, hcomm (u d) (x d e k)]
    exact isSymmetric_genericMultiplier _ hpar0
  · change IsSymmetric (pairParity (v d) (y d e k)) (sigma0 (v d) (y d e k)) _
    rw [sigma0, hcomm (v d) (y d e k)]
    exact isSymmetric_genericMultiplier _ hpar2
  · change IsSymmetric (pairParity (v d) (x d e k)) (sigma0 (v d) (x d e k)) _
    rw [sigma0, hcomm (v d) (x d e k)]
    exact isSymmetric_tailMultiplier (cutoff_bounds hneg).1 (pairParity_eq _ _)
      (inner_parity hneg) (neg_one_pow_sq _)
  · change IsRecurrent ((y d e k).exponent - (u d).exponent + 1) _ _
    rw [hP]
    exact isRecurrent_binomialMultiplier (RealInducedPairOuterTail.outerWeight_pos d e k)
      (pairParity_eq _ _) (outer_parity hneg)
  · change IsRecurrent ((x d e k).exponent - (u d).exponent + 1)
      (pairParity (u d) (x d e k)) (leftMultiplier d e k)
    rw [hA, hcomm (u d) (x d e k), leftMultiplier, add_zero]
    exact isRecurrent_genericMultiplier_of_ne hpar0 hg0.2
  · change IsRecurrent ((y d e k).exponent - (v d).exponent + 1)
      (pairParity (v d) (y d e k)) (rightMultiplier d e k)
    rw [hB, hcomm (v d) (y d e k), rightMultiplier, add_zero]
    exact isRecurrent_genericMultiplier_of_ne hpar2 hg2.2
  · change IsRecurrent ((x d e k).exponent - (v d).exponent + 1)
      (pairParity (v d) (x d e k)) (innerMultiplier d e k)
    rw [hcomm (v d) (x d e k)]
    convert hi using 1
    linear_combination -hh

section Maps

open RealCharacterWindowProjection RealAdjacentWindowSpanning
open RealBlockJacquet RealBlockFourierFinite

variable (hlink : IsLinkedAt d e k) (hneg : innerWeight d e k < 0)

abbrev leftWeight_pos : 0 < d.weight.natAbs :=
  lt_trans (cutoff_bounds hneg).1 (cutoff_bounds hneg).2.1

abbrev rightWeight_pos : 0 < e.weight.natAbs :=
  lt_trans (cutoff_bounds hneg).1 (cutoff_bounds hneg).2.2

abbrev quotientMap : KF 4 (P.X d e 0 (rightParity d e k)) →ₗ[ℂ] KF 4 [.induced d, .induced e] :=
  P.quotientMap d e 0 (rightParity d e k) (leftWeight_pos hneg) (rightWeight_pos hneg)

abbrev innerSwap : KF 4 (X1 d e 0 (rightParity d e k)) →ₗ[ℂ]
    KF 4 (P.X d e 0 (rightParity d e k)) :=
  blockFrobMap (incomingData hlink hneg).data3

abbrev middleSwap : KF 4 (X1 e d (rightParity d e k) 0) →ₗ[ℂ]
    KF 4 (X1 d e 0 (rightParity d e k)) :=
  RealInducedPairDistantParity.middle (incomingData hlink hneg)

/-- The incoming suffix after the first rank-one decomposition. -/
def afterOuter : KF 4 (X1 e d (rightParity d e k) 0) →ₗ[ℂ] KF 4 [.induced d, .induced e] :=
  (quotientMap hneg).comp ((innerSwap hlink hneg).comp (middleSwap hlink hneg))

theorem afterOuter_exact : IsRealIntertwinerModulo 4 (X1 e d (rightParity d e k) 0)
    [.induced d, .induced e] ⊥ (afterOuter hlink hneg) := by
  let m := incomingData hlink hneg
  exact modulo_comp_bot
    (RealInducedPairQuotientPresentation.quotient_exact d e 0 (rightParity d e k) _ _)
    (modulo_comp_bot
      (swap_exact (n := 4) (pre := [.character (u d)]) (post := [.character (y d e k)])
        rfl m.sym3 m.rec3)
      (RealInducedPairDistantParity.middle_exact m))

private theorem innerSwap_on_high (f : KF 4 (P.X d e 0 (rightParity d e k))) :
    highMiddle (u d) (v d) (x d e k) (y d e k) (innerCutoff d e k) f ∈
      LinearMap.range (innerSwap hlink hneg) := by
  let m := incomingData hlink hneg
  let hf := highMiddle (u d) (v d) (x d e k) (y d e k) (innerCutoff d e k) f
  let invData := data_unswap (n := 4) (pre := [.character (u d)]) (post := [.character (y d e k)])
    rfl m.sym3
  refine ⟨blockFrobMap invData hf, blockFrobMap_blockFrobMap_eq invData m.data3 hf ?_⟩
  intro j hj hprod g hg
  have hc := RealInducedSwapGeneric.pairParity_comm (v d) (x d e k)
  have hpar : Even ((innerCutoff d e k : ℤ) - 1 - pairParity (v d) (x d e k)) := by
    rw [hc]
    exact inner_parity hneg
  have hlt : |j| < (innerCutoff d e k : ℤ) := by
    by_contra hnot
    have hin : (innerCutoff d e k : ℤ) < |j| := by
      by_contra hle
      exact hnot (abs_lt_of_parity hpar hj (le_of_not_gt hle))
    have hj' : Even (j - pairParity (x d e k) (v d)) := by simpa only [hc] using hj
    have hm : innerMultiplier d e k j ≠ 0 :=
      (tailMultiplier_ne_zero_iff (cutoff_bounds hneg).1 (pairParity_eq _ _)
        (inner_parity hneg) (neg_one_pow_sq _) hj').mpr hin
    exact hprod (mul_inv_cancel₀ hm)
  exact (high_fourier (pre := [.character (u d)]) (post := [.character (y d e k)])
    (c := v d) (d := x d e k) rfl (cutoff_bounds hneg).1 hpar f j hg).trans
      (by rw [highMultiplier, lowMultiplier, ite_eq_left hlt, sub_self, zero_mul])

theorem afterOuter_surjective : Function.Surjective (afterOuter hlink hneg) := by
  let L := lowLeft (u d) (v d) (x d e k) (y d e k) d.weight.natAbs
  let H := highMiddle (u d) (v d) (x d e k) (y d e k) (innerCutoff d e k)
  have hpar : Even ((innerCutoff d e k : ℤ) - 1 - pairParity (v d) (x d e k)) := by
    rw [RealInducedSwapGeneric.pairParity_comm (v d) (x d e k)]
    exact inner_parity hneg
  have hspan : LinearMap.range L ⊔ LinearMap.range H = ⊤ :=
    four_spanning _ _ _ _ _ _ (leftWeight_pos hneg) (cutoff_bounds hneg).1 (cutoff_bounds hneg).2.1
      (RealInducedPairQuotientPresentation.pair_parity d 0) hpar
  have hkill (a : KF 4 (P.X d e 0 (rightParity d e k))) : quotientMap hneg (L a) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [quotientMap, RealInducedPairQuotientPresentation.ker_quotient]
    apply Submodule.mem_sup_left
    exact ⟨blockFrobMap (RealInducedPairQuotientPresentation.dataBd d e 0 (rightParity d e k)) a, rfl⟩
  intro z
  obtain ⟨f, rfl⟩ := RealInducedPairQuotientPresentation.quotient_surjective d e 0
    (rightParity d e k) (leftWeight_pos hneg) (rightWeight_pos hneg) z
  have hf : f ∈ LinearMap.range L ⊔ LinearMap.range H := by rw [hspan]; trivial
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨g, hg⟩ := innerSwap_on_high hlink hneg b
  obtain ⟨w, hw⟩ := RealInducedPairDistantParity.middle_surjective (incomingData hlink hneg)
    (fun _ _ => left_nonzero) (fun _ _ => right_nonzero hneg) g
  refine ⟨w, ?_⟩
  change quotientMap hneg (innerSwap hlink hneg (middleSwap hlink hneg w)) =
    quotientMap hneg (L a + H b)
  rw [hw, hg, map_add, hkill, zero_add]

/-- The swapped pair's map from the incoming word. -/
def swapMap : KF 4 [.induced e, .induced d] →ₗ[ℂ] KF 4 [.induced d, .induced e] :=
  (incomingData hlink hneg).swap (rightWeight_pos hneg) (leftWeight_pos hneg)

/-- The outer section followed by the actual incoming suffix. -/
def mixedMap : KF 4 (outerSource d e k) →ₗ[ℂ] KF 4 [.induced d, .induced e] :=
  (afterOuter hlink hneg).comp (RealInducedPairDistantParity.outerSection hlink (outer_parity hneg))

abbrev outerBinomial :=
  RealInducedPairDistantParity.outerBinomial d e k 0 (rightParity d e k)

private theorem beforeDescent_eq :
    (incomingData hlink hneg).beforeDescent (rightWeight_pos hneg) (leftWeight_pos hneg) =
      (afterOuter hlink hneg).comp (outerBinomial (d := d) (e := e) (k := k)) := by
  apply LinearMap.ext
  intro f
  rfl

theorem swapMap_exact : IsRealIntertwinerModulo 4 [.induced e, .induced d] [.induced d, .induced e]
    ⊥ (swapMap hlink hneg) :=
  ((incomingData hlink hneg).swap_descend (rightWeight_pos hneg) (leftWeight_pos hneg)).1

theorem mixedMap_modulo : IsRealIntertwinerModulo 4 (outerSource d e k) [.induced d, .induced e]
    (LinearMap.range (swapMap hlink hneg)) (mixedMap hlink hneg) := by
  have hr := ((incomingData hlink hneg).swap_descend (rightWeight_pos hneg) (leftWeight_pos hneg)).2.2
  change LinearMap.range (swapMap hlink hneg) = _ at hr
  rw [hr, beforeDescent_eq]
  exact RealInducedPairDistantFiltration.modulo_comp_range (afterOuter_exact hlink hneg)
    (RealInducedPairDistantParity.outer_decomposition hlink (outer_parity hneg)).1

theorem maps_span : ∀ z, ∃ a b, swapMap hlink hneg a + mixedMap hlink hneg b = z := by
  intro z
  obtain ⟨f, rfl⟩ := afterOuter_surjective hlink hneg z
  obtain ⟨a, b, hf⟩ :=
    (RealInducedPairDistantParity.outer_decomposition hlink (outer_parity hneg)).2 f
  let π := P.quotientMap e d (rightParity d e k) 0 (rightWeight_pos hneg) (leftWeight_pos hneg)
  refine ⟨π a, b, ?_⟩
  have hfac : (swapMap hlink hneg).comp π = (afterOuter hlink hneg).comp outerBinomial :=
    ((incomingData hlink hneg).swap_descend (rightWeight_pos hneg) (leftWeight_pos hneg)).2.1.trans
      (beforeDescent_eq hlink hneg)
  calc
    _ = afterOuter hlink hneg (outerBinomial a) + mixedMap hlink hneg b :=
      congrArg (fun w => w + mixedMap hlink hneg b) (LinearMap.congr_fun hfac a)
    _ = afterOuter hlink hneg
        (outerBinomial a + RealInducedPairDistantParity.outerSection hlink (outer_parity hneg) b) :=
      (map_add _ _ _).symm
    _ = afterOuter hlink hneg f := congrArg (afterOuter hlink hneg) hf

end Maps

end Langlands.Archimedean.RealInducedPairNegativeAscendingWord

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealInducedPairLinkedReplacement
  RealInducedPairNegativeAscendingWord

/-- The specified swapped-pair and mixed outer maps for negative inner
weight intertwine modulo their preceding range and span the original pair. -/
def RealInducedPairNegativeAscendingWordStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ) (hlink : IsLinkedAt d e k)
    (hneg : innerWeight d e k < 0),
      IsRealIntertwinerModulo 4 [.induced e, .induced d] [.induced d, .induced e] ⊥
        (swapMap hlink hneg) ∧
      IsRealIntertwinerModulo 4 (outerSource d e k) [.induced d, .induced e]
        (LinearMap.range (swapMap hlink hneg)) (mixedMap hlink hneg) ∧
      ∀ z, ∃ a b, swapMap hlink hneg a + mixedMap hlink hneg b = z

theorem realInducedPairNegativeAscendingWord : RealInducedPairNegativeAscendingWordStatement :=
  fun _ _ _ hlink hneg =>
    ⟨swapMap_exact hlink hneg, mixedMap_modulo hlink hneg, maps_span hlink hneg⟩

end Langlands.Archimedean
