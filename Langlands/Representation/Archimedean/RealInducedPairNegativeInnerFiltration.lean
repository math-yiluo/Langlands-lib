import Langlands.Representation.Archimedean.RealInducedPairNegativeInnerQuotient
import Langlands.Representation.Archimedean.RealInducedPairDistantParity

/-! # A two-piece filtration in the negative-inner-weight outer-square region -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairNegativeInnerFiltration

open RealStandardFiltration RealBlockFrobeniusMap RealBlockMultiplier
open RealCharacterPair RealCharacterPairReducible RealInducedPairAscendingExchange
open RealInducedPairLinkedReplacement RealInducedPairNegativeInnerQuotient

variable {d e : ComplexCharacterData} {k : ℕ}

/-- The final incoming crossing is a tail with the signs of the actual inner block. -/
def lastMultiplier (d e : ComplexCharacterData) (k : ℕ) : ℤ → ℂ :=
  tailMultiplier (innerWeight d e k).natAbs (pairParity (x e) (v d e k))
    ((-1 : ℂ) ^ (v d e k).parity.val)

theorem middle_pairParity :
    pairParity (v d e k) (x e) = pairParity (x e) (v d e k) := by
  unfold pairParity
  rw [add_comm]

theorem middle_sigma :
    sigma0 (v d e k) (x e) = (-1 : ℂ) ^ (v d e k).parity.val := by
  simp only [sigma0, pairParity, x, RealInducedPairQuotientPresentation.lo,
    RealJacquetFrobenius.charData, Fin.val_zero, add_zero,
    Nat.mod_eq_of_lt (v d e k).parity.isLt, Int.natAbs_natCast]

theorem tail_parity :
    Even (((innerWeight d e k).natAbs : ℤ) - 1 - pairParity (x e) (v d e k)) := by
  rw [← middle_pairParity]
  exact middle_parity

theorem outer_parity (hneg : innerWeight d e k < 0) :
    Even ((outerWeight d e k : ℤ) - 1 -
      pairParity (P.lo d (leftParity d e k)) (P.hi e 0)) := by
  have hs := RealInducedPairLinkedIncoming.weight_sum d e k
  have hc : ((innerWeight d e k).natAbs : ℤ) = -innerWeight d e k := by
    rw [Int.natCast_natAbs, abs_of_neg hneg]
  simp only [pairParity, RealInducedPairQuotientPresentation.lo,
    RealInducedPairQuotientPresentation.hi, RealJacquetFrobenius.charData, leftParity]
  rw [Int.even_iff]
  omega

/-- An outer binomial, two generic middle crossings, and the inner tail. -/
theorem exists_ascendingData (hlink : IsLinkedAt d e k) (hneg : innerWeight d e k < 0) :
    ∃ μ₀ μ₂ : ℤ → ℂ,
      MultiplierData e d 0 (leftParity d e k)
        (binomialMultiplier (outerWeight d e k)
          (pairParity (u d e k) (y e)))
        μ₀ μ₂ (lastMultiplier d e k) ∧
      (∀ j, Even (j - pairParity (u d e k) (x e)) → μ₀ j ≠ 0) ∧
      (∀ j, Even (j - pairParity (v d e k) (y e)) → μ₂ j ≠ 0) := by
  have hc : ((innerWeight d e k).natAbs : ℤ) = -innerWeight d e k := by
    rw [Int.natCast_natAbs, abs_of_neg hneg]
  have hp0 : Even (innerWeight d e k + (d.weight.natAbs : ℤ) -
      pairParity (u d e k) (x e)) := by
    simp only [pairParity, u, x, RealInducedPairQuotientPresentation.lo,
      RealJacquetFrobenius.charData, leftParity]
    rw [Int.even_iff]
    omega
  have hp2 : Even (innerWeight d e k + (e.weight.natAbs : ℤ) -
      pairParity (v d e k) (y e)) := by
    simp only [pairParity, v, y, RealInducedPairQuotientPresentation.hi,
      RealJacquetFrobenius.charData, leftParity]
    rw [Int.even_iff]
    omega
  obtain ⟨μ₀, hr0, hs0, hn0⟩ :=
    RealInducedPairDistantParity.exists_middle (u d e k) (x e) hp0
  obtain ⟨μ₂, hr2, hs2, hn2⟩ :=
    RealInducedPairDistantParity.exists_middle (v d e k) (y e) hp2
  obtain ⟨hν1, hν0, hν2, hν3⟩ :=
    RealInducedPairDistantParity.differences (sd := leftParity d e k) (se := 0) hlink
  refine ⟨μ₀, μ₂, ⟨?_, hs0, hs2, ?_, ?_, ?_, ?_, ?_⟩, hn0, hn2⟩
  · exact isSymmetric_binomialMultiplier _ (pairParity_eq _ _)
  · rw [middle_sigma, middle_pairParity]
    exact isSymmetric_tailMultiplier (cutoff_bounds hneg).1 (pairParity_eq _ _)
      tail_parity (neg_one_pow_sq_fin _)
  · rw [hν1]
    exact isRecurrent_binomialMultiplier (RealInducedPairOuterTail.outerWeight_pos d e k)
      (pairParity_eq _ _) (outer_parity hneg)
  · rw [hν0]
    simpa only [Int.cast_add, Int.cast_natCast] using hr0
  · rw [hν2]
    simpa only [Int.cast_add, Int.cast_natCast] using hr2
  · rw [hν3, middle_pairParity]
    have hcc : ((innerWeight d e k).natAbs : ℂ) = -(innerWeight d e k : ℂ) := by
      simpa only [Int.cast_natCast, Int.cast_neg] using
        congrArg (fun z : ℤ => (z : ℂ)) hc
    convert isRecurrent_tailMultiplier (cutoff_bounds hneg).1 (pairParity_eq (x e) (v d e k))
      tail_parity (neg_one_pow_sq_fin (v d e k).parity) using 1
    · rw [hcc]
      ring
    · rfl

section Last

variable (hlink : IsLinkedAt d e k) (hneg : innerWeight d e k < 0)

abbrev lastData :=
  data_D (n := 4) (pre := [.character (u d e k)]) (post := [.character (y e)])
    rfl (cutoff_bounds hneg).1 tail_parity (middle_gap hlink hneg)

abbrev lastSectionData :=
  data_q1 (n := 4) (pre := [.character (u d e k)]) (post := [.character (y e)])
    rfl (cutoff_bounds hneg).1 tail_parity (middle_gap hlink hneg)

/-- The actual final tail with the middle-induced codomain retained. -/
def lastToMiddle :
    KF 4 (X1 d e (leftParity d e k) 0) →ₗ[ℂ] KF 4 (middleList d e k) :=
  blockFrobMap (lastData hlink hneg)

theorem lastToMiddle_surjective : Function.Surjective (lastToMiddle hlink hneg) := by
  intro f
  refine ⟨blockFrobMap (lastSectionData hlink hneg) f, ?_⟩
  exact RealCharacterInducedPushforward.tail_inv (cutoff_bounds hneg).1 (pairParity_eq _ _)
    tail_parity (neg_one_pow_sq_fin _) (lastData hlink hneg) (lastSectionData hlink hneg)
    rfl (by simp only [pairInduced_weight, Int.abs_eq_natAbs, Int.natAbs_natCast]) f

variable {μ₀ μ₂ : ℤ → ℂ}
  (hm : MultiplierData e d 0 (leftParity d e k)
    (binomialMultiplier (outerWeight d e k) (pairParity (u d e k) (y e)))
    μ₀ μ₂ (lastMultiplier d e k))

theorem last_factor (f : KF 4 (X1 d e (leftParity d e k) 0)) :
    blockFrobMap hm.data3 f =
      middleInclusion hlink hneg (lastToMiddle hlink hneg f) := by
  apply eq_of_blockFourierCoefficient_eq (show 1 + 1 < 4 by decide)
  intro j g hg
  calc
    _ = lastMultiplier d e k j * blockFourierCoefficient 4 1 j f g :=
      blockFourierCoefficient_blockFrobMap hm.data3 f hg j
    _ = _ := (blockFourierCoefficient_blockFrobMap (lastData hlink hneg) f hg j).symm

def suffix : KF 4 (X1 e d 0 (leftParity d e k)) →ₗ[ℂ]
    KF 4 (P.X d e (leftParity d e k) 0) :=
  (blockFrobMap hm.data3).comp (RealInducedPairDistantParity.middle hm)

theorem suffix_exact :
    IsRealIntertwinerModulo 4 (X1 e d 0 (leftParity d e k))
      (P.X d e (leftParity d e k) 0) ⊥ (suffix hm) :=
  modulo_comp_bot
    (swap_exact (n := 4) (pre := [.character (u d e k)])
      (post := [.character (y e)]) rfl hm.sym3 hm.rec3)
    (RealInducedPairDistantParity.middle_exact hm)

include hlink hneg in
theorem quotient_suffix_surjective
    (hn0 : ∀ j, Even (j - pairParity (u d e k) (x e)) → μ₀ j ≠ 0)
    (hn2 : ∀ j, Even (j - pairParity (v d e k) (y e)) → μ₂ j ≠ 0)
    (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) :
    Function.Surjective ((P.quotientMap d e (leftParity d e k) 0 hd he).comp (suffix hm)) := by
  intro z
  obtain ⟨f, rfl⟩ := RealInducedPairNegativeInnerQuotient.quotient_surjective hlink hneg z
  obtain ⟨g, hg⟩ := lastToMiddle_surjective hlink hneg f
  obtain ⟨w, hw⟩ := RealInducedPairDistantParity.middle_surjective hm hn0 hn2 g
  refine ⟨w, ?_⟩
  change P.quotientMap d e (leftParity d e k) 0 hd he
    (blockFrobMap hm.data3 (RealInducedPairDistantParity.middle hm w)) = _
  rw [hw, last_factor hlink hneg hm g, hg]
  rfl

theorem beforeDescent_eq (hd : 0 < d.weight.natAbs) (he : 0 < e.weight.natAbs) :
    hm.beforeDescent he hd =
      ((P.quotientMap d e (leftParity d e k) 0 hd he).comp (suffix hm)).comp
        (RealInducedPairDistantParity.outerBinomial d e k (leftParity d e k) 0) := by
  apply LinearMap.ext
  intro f
  rfl

end Last

/-- An actual two-piece filtration, with an arbitrary predicate on its two source lists. -/
theorem filtration_of_pieces (hlink : IsLinkedAt d e k) (hneg : innerWeight d e k < 0)
    {C : List RealBlock → Prop} (hW : C [.induced e, .induced d])
    (hR : C (RealInducedPairDistantParity.outerPiece d e k (leftParity d e k) 0)) :
    HasFiltration 4 [.induced d, .induced e] C := by
  have hd : 0 < d.weight.natAbs := lt_trans (cutoff_bounds hneg).1 (cutoff_bounds hneg).2.1
  have he : 0 < e.weight.natAbs := lt_trans (cutoff_bounds hneg).1 (cutoff_bounds hneg).2.2
  obtain ⟨μ₀, μ₂, hm, hn0, hn2⟩ := exists_ascendingData hlink hneg
  let A := (P.quotientMap d e (leftParity d e k) 0 hd he).comp (suffix hm)
  have hA : IsRealIntertwinerModulo 4 (X1 e d 0 (leftParity d e k))
      [.induced d, .induced e] ⊥ A :=
    modulo_comp_bot (RealInducedPairQuotientPresentation.quotient_exact d e (leftParity d e k) 0 hd he)
      (suffix_exact hm)
  have hAs : Function.Surjective A := quotient_suffix_surjective hlink hneg hm hn0 hn2 hd he
  obtain ⟨hq, hfac, hrange⟩ := hm.swap_descend he hd
  have hfac' := hfac.trans (beforeDescent_eq hm hd he)
  have hrange' := hrange.trans (congrArg LinearMap.range (beforeDescent_eq hm hd he))
  let s := RealInducedPairDistantParity.outerSection hlink (outer_parity hneg)
  let qR := A.comp s
  have hqR : IsRealIntertwinerModulo 4
      (RealInducedPairDistantParity.outerPiece d e k (leftParity d e k) 0) [.induced d, .induced e]
      (LinearMap.range (hm.swap he hd)) qR := by
    rw [hrange']
    exact RealInducedPairDistantFiltration.modulo_comp_range hA
      (RealInducedPairDistantParity.outer_decomposition hlink (outer_parity hneg)).1
  apply RealCharacterInducedPushforward.hasFiltration_two hW hR (hm.swap he hd) qR hq hqR
  intro z
  obtain ⟨f, rfl⟩ := hAs z
  obtain ⟨a, r, hf⟩ :=
    (RealInducedPairDistantParity.outer_decomposition hlink (outer_parity hneg)).2 f
  refine ⟨P.quotientMap e d 0 (leftParity d e k) he hd a, r, ?_⟩
  change (hm.swap he hd) (P.quotientMap e d 0 (leftParity d e k) he hd a) + A (s r) = A f
  have ha : (hm.swap he hd) (P.quotientMap e d 0 (leftParity d e k) he hd a) =
      A (RealInducedPairDistantParity.outerBinomial d e k (leftParity d e k) 0 a) :=
    LinearMap.congr_fun hfac' a
  rw [ha, ← map_add, hf]

theorem filtration (hlink : IsLinkedAt d e k) (hneg : innerWeight d e k < 0)
    (hb : d.weight.natAbs ^ 2 + e.weight.natAbs ^ 2 < outerWeight d e k ^ 2) :
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e) := by
  apply (realAdjacentFiltration_iff 4 [] [] (.induced d) (.induced e)).mpr
  apply filtration_of_pieces hlink hneg
  · exact ⟨[.induced e, .induced d], rfl, Or.inl rfl⟩
  · refine ⟨RealInducedPairDistantParity.outerPiece d e k (leftParity d e k) 0, rfl,
      Or.inr ⟨RealInducedPairDistantParity.outer_support hlink, ?_⟩⟩
    rw [RealInducedPairDistantParity.outer_weightSquareSum]
    simpa [realWeightSquareSum, realBlockWeightSquare] using hb

end RealInducedPairNegativeInnerFiltration

/-- Negative signed inner weight and a sufficiently large outer square give the actual
adjacent filtration of the original two induction blocks, with no parity hypothesis. -/
def RealInducedPairNegativeInnerFiltrationStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ),
    RealInducedPairLinkedReplacement.IsLinkedAt d e k →
    RealInducedPairLinkedReplacement.innerWeight d e k < 0 →
    d.weight.natAbs ^ 2 + e.weight.natAbs ^ 2 <
      RealInducedPairLinkedReplacement.outerWeight d e k ^ 2 →
    RealAdjacentFiltration 4 [] [] (.induced d) (.induced e)

theorem realInducedPairNegativeInnerFiltration : RealInducedPairNegativeInnerFiltrationStatement :=
  fun _ _ _ hlink hneg hb => RealInducedPairNegativeInnerFiltration.filtration hlink hneg hb

end Langlands.Archimedean
