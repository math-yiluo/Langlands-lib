import Langlands.Representation.Archimedean.RealInducedPairNegativeInnerFiltration
import Langlands.Representation.Archimedean.RealStandardEquivStages
import Langlands.Representation.Archimedean.RealCharacterInducedInterlaced
import Langlands.Representation.Archimedean.RealInducedSwapArithmetic

/-! # The actual replacement quotient of the negative-inner outer source -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealInducedPairNegativeOuterQuotient

open RealStandardFiltration RealBlockFrobeniusMap RealCharacterPair RealCharacterPairReducible
open RealInducedPairLinkedReplacement RealInducedPairNegativeInnerQuotient
open RealCharacterInducedSwap RealCharacterInducedInterlaced InductionStages

variable (d e : ComplexCharacterData) (k : ℕ)

abbrev rawOuter : ComplexCharacterData :=
  pairInduced (u d e k) (y e) (outerWeight d e k)

abbrev source : List RealBlock :=
  RealInducedPairDistantParity.outerPiece d e k (leftParity d e k) 0

abbrev exposed : List RealBlock :=
  [.induced (rawOuter d e k), .character (x e), .character (v d e k)]

abbrev fused : List RealBlock :=
  [.induced (rawOuter d e k), .induced (middleData d e k)]

theorem rawOuter_eq : rawOuter d e k = outerData d e k := by
  unfold rawOuter pairInduced outerData
  congr 1
  change ((d.exponent - (d.weight.natAbs : ℂ) / 2) +
    (e.exponent + (e.weight.natAbs : ℂ) / 2)) / 2 = outerExponent d e
  unfold outerExponent
  ring

theorem middle_exponent : (middleData d e k).exponent = (innerData d e k).exponent := by
  change ((e.exponent - (e.weight.natAbs : ℂ) / 2) +
    (d.exponent + (d.weight.natAbs : ℂ) / 2)) / 2 = innerExponent d e
  unfold innerExponent
  ring

theorem kf_fused : KF 4 (fused d e k) = KF 4 (replacementPair d e k) := by
  rw [show fused d e k = [.induced (outerData d e k), .induced (middleData d e k)] by
    rw [fused, rawOuter_eq]]
  apply congrArg (fun M => kFiniteFunctions M (unitaryCompact ℝ 4))
  exact RealInducedSwapArithmetic.standardModule_replace_induced 4
    [.induced (outerData d e k)] [] (by
      simp only [middleData, pairInduced_weight, innerData, characterOfParams_weight,
        Int.natAbs_natCast]) (middle_exponent d e k)

variable {d e k} (hlink : IsLinkedAt d e k) (hneg : innerWeight d e k < 0)

include hneg in
theorem interlacing_bounds :
    0 < d.weight.natAbs - (innerWeight d e k).natAbs ∧
      d.weight.natAbs - (innerWeight d e k).natAbs < (rawOuter d e k).weight.natAbs := by
  have hb := cutoff_bounds hneg
  have hm := le_max_left d.weight.natAbs e.weight.natAbs
  simp only [rawOuter, pairInduced_weight, Int.natAbs_natCast]
  unfold outerWeight
  omega

include hlink hneg in
theorem interlacing_gap :
    (chB (rawOuter d e k)).exponent - (x e).exponent =
      -((d.weight.natAbs - (innerWeight d e k).natAbs : ℕ) : ℂ) := by
  have hP := (RealInducedPairDistantParity.differences
    (sd := leftParity d e k) (se := 0) hlink).1
  have hL := RealInducedPairQuotientPresentation.hi_sub_lo d (leftParity d e k)
  have hh := middle_gap hlink hneg
  rw [Nat.cast_sub (cutoff_bounds hneg).2.1.le]
  change (((u d e k).exponent + (y e).exponent) / 2 -
    (outerWeight d e k : ℂ) / 2) - (x e).exponent = _
  linear_combination hP / 2 - hL + hh

def localEquiv :
    KFin 3 (lCD (x e) (rawOuter d e k)) ≃ₗ[ℂ] KFin 3 (lDC (x e) (rawOuter d e k)) :=
  interlacedEquiv (x e) (rawOuter d e k) (interlacing_bounds hneg).1
    (interlacing_bounds hneg).2 (interlacing_gap hlink hneg)

theorem localEquiv_exact :
    IsRealStandardIntertwiner 3 (realStandardRep 3 (lDC (x e) (rawOuter d e k)))
      (realStandardLie 3 (lDC (x e) (rawOuter d e k)))
      (lCD (x e) (rawOuter d e k)) (localEquiv hlink hneg).toLinearMap :=
  interlacedEquiv_isIntertwiner (x e) (rawOuter d e k) (interlacing_bounds hneg).1
    (interlacing_bounds hneg).2 (interlacing_gap hlink hneg)

/-- Reorder the left inner character past the outer induction block. -/
def exposeEquiv : KF 4 (source d e k) ≃ₗ[ℂ] KF 4 (exposed d e k) :=
  standardEquivInd (n := 4) (a := 0) (r := 3)
    (ds := lCD (x e) (rawOuter d e k)) (es := lDC (x e) (rawOuter d e k))
    (pre := []) (post := [.character (v d e k)])
    (by decide : 0 + 3 ≤ 4) rfl rfl rfl rfl
    (localEquiv hlink hneg) (localEquiv_exact hlink hneg)

theorem modulo_of_standard {n : ℕ} {ds es : List RealBlock}
    {T : KF n ds →ₗ[ℂ] KF n es}
    (hT : IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T) :
    IsRealIntertwinerModulo n ds es ⊥ T := by
  obtain ⟨hk, hl⟩ := isRealStandardIntertwiner_iff.mp hT
  apply isRealIntertwinerModulo_iff.mpr
  exact ⟨fun κ f => by rw [hk, sub_self]; exact Submodule.zero_mem _,
    fun A f => by rw [hl, sub_self]; exact Submodule.zero_mem _⟩

theorem exposeEquiv_exact :
    IsRealIntertwinerModulo 4 (source d e k) (exposed d e k) ⊥
      (exposeEquiv hlink hneg).toLinearMap :=
  modulo_of_standard (standardEquivInd_intertwiner (n := 4) (a := 0) (r := 3)
    (ds := lCD (x e) (rawOuter d e k)) (es := lDC (x e) (rawOuter d e k))
    (pre := []) (post := [.character (v d e k)])
    (by decide : 0 + 3 ≤ 4) rfl rfl rfl rfl
    (localEquiv hlink hneg) (localEquiv_exact hlink hneg))

abbrev innerTailData :=
  data_D (n := 4) (pre := [.induced (rawOuter d e k)]) (post := [])
    rfl (cutoff_bounds hneg).1
    RealInducedPairNegativeInnerFiltration.tail_parity (middle_gap hlink hneg)

abbrev innerSectionData :=
  data_q1 (n := 4) (pre := [.induced (rawOuter d e k)]) (post := [])
    rfl (cutoff_bounds hneg).1
    RealInducedPairNegativeInnerFiltration.tail_parity (middle_gap hlink hneg)

abbrev innerBinomialData :=
  data_q0 (n := 4) (ℓ := (innerWeight d e k).natAbs)
    (pre := [.induced (rawOuter d e k)]) (post := [])
    (c := x e) (d := v d e k) rfl

abbrev innerInverseBinomialData :=
  data_B (n := 4) (ℓ := (innerWeight d e k).natAbs)
    (pre := [.induced (rawOuter d e k)]) (post := [])
    (c := x e) (d := v d e k) rfl

/-- The replacement quotient of the mixed outer source used in the two-piece filtration. -/
def replacementQuotient : KF 4 (source d e k) →ₗ[ℂ] KF 4 (replacementPair d e k) :=
  (ofEqMap (kf_fused d e k)).comp
    ((blockFrobMap (innerTailData hlink hneg)).comp (exposeEquiv hlink hneg).toLinearMap)

theorem replacementQuotient_exact :
    IsRealIntertwinerModulo 4 (source d e k) (replacementPair d e k) ⊥
      (replacementQuotient hlink hneg) :=
  modulo_comp_bot (modulo_ofEqMap (kf_fused d e k))
    (modulo_comp_bot
      (RealInducedPairQuotientPresentation.tail_exact (n := 4)
        (pre := [.induced (rawOuter d e k)]) (post := []) rfl
        (cutoff_bounds hneg).1 RealInducedPairNegativeInnerFiltration.tail_parity
        (middle_gap hlink hneg))
      (exposeEquiv_exact hlink hneg))

theorem replacementQuotient_surjective : Function.Surjective (replacementQuotient hlink hneg) := by
  have htail : Function.Surjective (blockFrobMap (innerTailData hlink hneg)) := by
    intro f
    refine ⟨blockFrobMap (innerSectionData hlink hneg) f, ?_⟩
    exact RealCharacterInducedPushforward.tail_inv (cutoff_bounds hneg).1 (pairParity_eq _ _)
      RealInducedPairNegativeInnerFiltration.tail_parity (neg_one_pow_sq_fin _)
      (innerTailData hlink hneg) (innerSectionData hlink hneg) rfl
      (by simp only [pairInduced_weight, Int.abs_eq_natAbs, Int.natAbs_natCast]) f
  exact (ofEqMap_surjective (kf_fused d e k)).comp
    (htail.comp (exposeEquiv hlink hneg).surjective)

/-- Its kernel is exactly the exposed inner-binomial image pulled back across the equivalence. -/
theorem ker_replacementQuotient :
    LinearMap.ker (replacementQuotient hlink hneg) =
      (LinearMap.range (blockFrobMap (innerBinomialData (d := d) (e := e) (k := k)))).comap
        (exposeEquiv hlink hneg).toLinearMap := by
  unfold replacementQuotient
  rw [RealInducedPairOuterTail.ker_ofEqMap_comp, LinearMap.ker_comp]
  rw [RealInducedPairQuotientPresentation.ker_tail_eq_range
    (cutoff_bounds hneg).1 (pairParity_eq _ _)
    RealInducedPairNegativeInnerFiltration.tail_parity (neg_one_pow_sq_fin _)
    (innerBinomialData (d := d) (e := e) (k := k))
    (innerInverseBinomialData (d := d) (e := e) (k := k)) (innerTailData hlink hneg)]

end RealInducedPairNegativeOuterQuotient

/-- For every linked negative-inner pair, its mixed outer source has an actual surjective
exact quotient onto the heavier replacement pair. -/
def RealInducedPairNegativeOuterQuotientStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ),
    RealInducedPairLinkedReplacement.IsLinkedAt d e k →
    RealInducedPairLinkedReplacement.innerWeight d e k < 0 →
    ∃ T : RealStandardFiltration.KF 4 (RealInducedPairNegativeOuterQuotient.source d e k) →ₗ[ℂ]
      RealStandardFiltration.KF 4 (RealInducedPairLinkedReplacement.replacementPair d e k),
      IsRealIntertwinerModulo 4 (RealInducedPairNegativeOuterQuotient.source d e k)
        (RealInducedPairLinkedReplacement.replacementPair d e k) ⊥ T ∧
      Function.Surjective T

theorem realInducedPairNegativeOuterQuotient : RealInducedPairNegativeOuterQuotientStatement :=
  fun _ _ _ hlink hneg =>
    ⟨RealInducedPairNegativeOuterQuotient.replacementQuotient hlink hneg,
      RealInducedPairNegativeOuterQuotient.replacementQuotient_exact hlink hneg,
      RealInducedPairNegativeOuterQuotient.replacementQuotient_surjective hlink hneg⟩

end Langlands.Archimedean
