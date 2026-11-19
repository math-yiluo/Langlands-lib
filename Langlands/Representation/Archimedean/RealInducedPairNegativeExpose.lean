import Langlands.Representation.Archimedean.RealInducedPairNegativeAscendingWord
import Langlands.Representation.Archimedean.RealInducedPairVisibleOuterQuotient

/-! # Forward exposure of the negative-inner replacement quotient -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealInducedPairNegativeExpose

open Langlands.LocalFactor.Archimedean RealStandardFiltration RealBlockFrobeniusMap
  RealBlockFourierFinite RealCharacterPair RealCharacterPairReducible
  RealInducedPairLinkedReplacement RealInducedPairNegativeAscendingWord
  RealCharacterInducedSwap InductionStages
open RealInducedPairNegativeInnerQuotient (cutoff_bounds)

abbrev outerBlock (d e : ComplexCharacterData) (k : ℕ) :=
  pairInduced (u d) (y d e k) (outerWeight d e k)

abbrev exposed (d e : ComplexCharacterData) (k : ℕ) : List RealBlock :=
  [.induced (outerBlock d e k), .character (x d e k), .character (v d)]

abbrev fused (d e : ComplexCharacterData) (k : ℕ) : List RealBlock :=
  [.induced (outerBlock d e k), .induced (pairInduced (x d e k) (v d) (innerCutoff d e k))]

variable {d e : ComplexCharacterData} {k : ℕ}
  (hlink : IsLinkedAt d e k) (hneg : innerWeight d e k < 0)

private theorem kf_fused : KF 4 (fused d e k) = KF 4 (replacementPair d e k) :=
  RealInducedPairNegativeOuterQuotient.kf_fused d e k

include hlink hneg in
theorem chB_outer : chB (outerBlock d e k) = u d := by
  have h := (gaps hlink hneg).1
  change RealJacquetFrobenius.charData 0
    (((u d).exponent + (y d e k).exponent) / 2 - (outerWeight d e k : ℂ) / 2) = _
  change _ = RealJacquetFrobenius.charData 0 (u d).exponent
  congr 1
  linear_combination h / 2

include hlink hneg in
theorem chA_outer : chA (outerBlock d e k) = y d e k := by
  have h := (gaps hlink hneg).1
  have hpar : RealCharacterInducedPushforward.fin2 (outerWeight d e k + 1) = (y d e k).parity := by
    apply Fin.ext
    rw [RealCharacterInducedPushforward.fin2_val, y_parity_val]
    have hp := (gaps_add hneg).2.2.1
    omega
  change RealJacquetFrobenius.charData
    (RealCharacterInducedPushforward.fin2 (outerWeight d e k + 1))
    (((u d).exponent + (y d e k).exponent) / 2 + (outerWeight d e k : ℂ) / 2) = _
  rw [hpar]
  change _ = RealJacquetFrobenius.charData (y d e k).parity (y d e k).exponent
  congr 1
  linear_combination -h / 2

include hneg in
private theorem interlacing_bounds :
    0 < leftGap d e k ∧ leftGap d e k < (outerBlock d e k).weight.natAbs := by
  have hp := (gaps_add hneg).2.2.1
  have hM := rightWeight_pos hneg
  change 0 < leftGap d e k ∧ leftGap d e k < outerWeight d e k
  exact ⟨(gap_bounds hneg).1, by omega⟩

include hlink hneg in
private theorem interlacing_gap :
    (chB (outerBlock d e k)).exponent - (x d e k).exponent = -(leftGap d e k : ℂ) := by
  rw [chB_outer hlink hneg]
  linear_combination -(gaps hlink hneg).2.1

private theorem forward_parity : (leftGap d e k + (x d e k).parity.val) % 2 = 0 := by
  rw [x_parity_val]
  omega

def localEquiv : KFin 3 (lCD (x d e k) (outerBlock d e k)) ≃ₗ[ℂ]
    KFin 3 (lDC (x d e k) (outerBlock d e k)) :=
  RealVisibleInterlaced.equiv _ _ (interlacing_bounds hneg).1 (interlacing_bounds hneg).2
    (interlacing_gap hlink hneg)

private theorem localEquiv_exact :
    IsRealStandardIntertwiner 3 (realStandardRep 3 (lDC (x d e k) (outerBlock d e k)))
      (realStandardLie 3 (lDC (x d e k) (outerBlock d e k)))
      (lCD (x d e k) (outerBlock d e k)) (localEquiv hlink hneg).toLinearMap := by
  have hm := RealVisibleInterlaced.equiv_exact (x d e k) (outerBlock d e k)
    (interlacing_bounds hneg).1 (interlacing_bounds hneg).2 (interlacing_gap hlink hneg)
  simpa only [LinearMap.id_comp, localEquiv] using
    hm.comp (isRealStandardIntertwiner_id 3 (lDC (x d e k) (outerBlock d e k))) bot_le

def expose : KF 4 (outerSource d e k) ≃ₗ[ℂ] KF 4 (exposed d e k) :=
  standardEquivInd (n := 4) (a := 0) (r := 3)
    (ds := lCD (x d e k) (outerBlock d e k)) (es := lDC (x d e k) (outerBlock d e k))
    (pre := []) (post := [.character (v d)]) (by decide : 0 + 3 ≤ 4) rfl rfl rfl rfl
    (localEquiv hlink hneg) (localEquiv_exact hlink hneg)

theorem expose_exact : IsRealIntertwinerModulo 4 (outerSource d e k) (exposed d e k) ⊥
    (expose hlink hneg).toLinearMap :=
  RealInducedPairNegativeOuterQuotient.modulo_of_standard
    (standardEquivInd_intertwiner (n := 4) (a := 0) (r := 3)
      (ds := lCD (x d e k) (outerBlock d e k)) (es := lDC (x d e k) (outerBlock d e k))
      (pre := []) (post := [.character (v d)]) (by decide : 0 + 3 ≤ 4) rfl rfl rfl rfl
      (localEquiv hlink hneg) (localEquiv_exact hlink hneg))

abbrev sourceSlice (κ : unitaryCompact ℝ 4) :
    KF 4 (outerSource d e k) →ₗ[ℂ] KFin 3 (lCD (x d e k) (outerBlock d e k)) :=
  sliceK (n := 4) (a := 0) (r := 3) (pre := []) (post := [.character (v d)])
    (ds := lCD (x d e k) (outerBlock d e k))
    (by decide : 0 + 3 ≤ 4) rfl rfl κ

abbrev exposedSlice (κ : unitaryCompact ℝ 4) :
    KF 4 (exposed d e k) →ₗ[ℂ] KFin 3 (lDC (x d e k) (outerBlock d e k)) :=
  sliceK (n := 4) (a := 0) (r := 3) (pre := []) (post := [.character (v d)])
    (ds := lDC (x d e k) (outerBlock d e k))
    (by decide : 0 + 3 ≤ 4) rfl rfl κ

/-- Because the left gap has the parity of `x`, every slice uses the forward word. -/
theorem expose_forward_formula :
    ∃ (h₀ : RealVisibleInterlaced.SecondTailData (x d e k) (outerBlock d e k) (leftGap d e k))
      (h₁ : RealVisibleInterlaced.SecondGenericData (x d e k) (outerBlock d e k) (leftGap d e k)),
      ∀ κ f, (exposedSlice κ (expose hlink hneg f) : Langlands.GeneralLinear 3 ℝ → ℂ) =
        blockFrobMap h₁ (blockFrobMap h₀ (sourceSlice κ f)) := by
  obtain ⟨h₀, h₁, hf⟩ := RealVisibleInterlaced.equiv_forward_formula (x d e k) (outerBlock d e k)
    (interlacing_bounds hneg).1 (interlacing_bounds hneg).2
    (interlacing_gap hlink hneg) forward_parity
  refine ⟨h₀, h₁, fun κ f => ?_⟩
  have hs : exposedSlice κ (expose hlink hneg f) = localEquiv hlink hneg (sourceSlice κ f) :=
    sliceK_standardEquivInd (n := 4) (a := 0) (r := 3)
    (ds := lCD (x d e k) (outerBlock d e k)) (es := lDC (x d e k) (outerBlock d e k))
    (pre := []) (post := [.character (v d)]) (by decide : 0 + 3 ≤ 4) rfl rfl rfl rfl
    (localEquiv hlink hneg) (localEquiv_exact hlink hneg) κ f
  exact (congrArg Subtype.val hs).trans (hf (sourceSlice κ f))

abbrev innerData := data_D (n := 4) (pre := [.induced (outerBlock d e k)]) (post := [])
  rfl (cutoff_bounds hneg).1 (inner_parity hneg) (gaps hlink hneg).2.2.2

abbrev innerSectionData := data_q1 (n := 4) (pre := [.induced (outerBlock d e k)]) (post := [])
  rfl (cutoff_bounds hneg).1 (inner_parity hneg) (gaps hlink hneg).2.2.2

/-- Expose the inner character pair and take its actual tail quotient. -/
def replacementQuotient : KF 4 (outerSource d e k) →ₗ[ℂ] KF 4 (replacementPair d e k) :=
  (ofEqMap (kf_fused (d := d) (e := e) (k := k))).comp
    ((blockFrobMap (innerData hlink hneg)).comp (expose hlink hneg).toLinearMap)

theorem replacementQuotient_exact :
    IsRealIntertwinerModulo 4 (outerSource d e k) (replacementPair d e k) ⊥
      (replacementQuotient hlink hneg) :=
  modulo_comp_bot (modulo_ofEqMap (kf_fused (d := d) (e := e) (k := k)))
    (modulo_comp_bot
      (RealInducedPairQuotientPresentation.tail_exact (n := 4)
        (pre := [.induced (outerBlock d e k)]) (post := []) rfl
        (cutoff_bounds hneg).1 (inner_parity hneg) (gaps hlink hneg).2.2.2)
      (expose_exact hlink hneg))

theorem replacementQuotient_surjective : Function.Surjective (replacementQuotient hlink hneg) := by
  have htail : Function.Surjective (blockFrobMap (innerData hlink hneg)) := by
    intro f
    refine ⟨blockFrobMap (innerSectionData hlink hneg) f, ?_⟩
    exact RealCharacterInducedPushforward.tail_inv (cutoff_bounds hneg).1 (pairParity_eq _ _)
      (inner_parity hneg) (neg_one_pow_sq_fin _) (innerData hlink hneg) (innerSectionData hlink hneg)
      rfl (by simp only [pairInduced_weight, Int.abs_eq_natAbs, Int.natAbs_natCast]) f
  exact (ofEqMap_surjective (kf_fused (d := d) (e := e) (k := k))).comp
    (htail.comp (expose hlink hneg).surjective)

theorem replacementQuotient_eq_zero (f : KF 4 (outerSource d e k)) :
    replacementQuotient hlink hneg f = 0 ↔
      ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, (innerCutoff d e k : ℤ) ≤ |j| →
        blockFourierCoefficient 4 2 j (expose hlink hneg f) g = 0 := by
  unfold replacementQuotient
  rw [LinearMap.comp_apply, RealInducedPairOuterTail.ofEqMap_eq_zero_iff]
  exact RealInducedPairOuterTail.tail_eq_zero_iff (cutoff_bounds hneg).1 (pairParity_eq _ _)
    (inner_parity hneg) (neg_one_pow_sq_fin _) (innerData hlink hneg) (expose hlink hneg f)

end Langlands.Archimedean.RealInducedPairNegativeExpose

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealStandardFiltration RealBlockFrobeniusMap
  RealBlockFourierFinite RealInducedPairLinkedReplacement RealInducedPairNegativeAscendingWord
  RealInducedPairNegativeExpose

/-- The negative-inner replacement quotient with the forward compact slice
formula for the selected ascending endpoint parities. -/
def RealInducedPairNegativeExposeStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ) (hlink : IsLinkedAt d e k)
    (hneg : innerWeight d e k < 0),
    IsRealIntertwinerModulo 4 (outerSource d e k) (replacementPair d e k) ⊥
      (replacementQuotient hlink hneg) ∧
    Function.Surjective (replacementQuotient hlink hneg) ∧
    (∀ f : KF 4 (outerSource d e k), replacementQuotient hlink hneg f = 0 ↔
      ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, (innerCutoff d e k : ℤ) ≤ |j| →
        blockFourierCoefficient 4 2 j (expose hlink hneg f) g = 0) ∧
    (∃ (h₀ : RealVisibleInterlaced.SecondTailData (x d e k) (outerBlock d e k) (leftGap d e k))
      (h₁ : RealVisibleInterlaced.SecondGenericData (x d e k) (outerBlock d e k) (leftGap d e k)),
        ∀ κ f, (exposedSlice κ (expose hlink hneg f) : Langlands.GeneralLinear 3 ℝ → ℂ) =
          blockFrobMap h₁ (blockFrobMap h₀ (sourceSlice κ f)))

theorem realInducedPairNegativeExpose : RealInducedPairNegativeExposeStatement :=
  fun _ _ _ hlink hneg =>
    ⟨replacementQuotient_exact hlink hneg, replacementQuotient_surjective hlink hneg,
      replacementQuotient_eq_zero hlink hneg, expose_forward_formula hlink hneg⟩

end Langlands.Archimedean
