import Langlands.Representation.Archimedean.RealInducedPairNegativeOuterQuotient
import Langlands.Representation.Archimedean.RealVisibleInterlaced

/-! # The negative outer quotient with explicit interlaced compact-slice formulas -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean
open Langlands.LocalFactor.Archimedean
attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealInducedPairVisibleOuterQuotient

open RealStandardFiltration RealBlockFrobeniusMap RealCharacterPairReducible RealCharacterPair
open RealInducedPairLinkedReplacement RealInducedPairNegativeInnerQuotient
open RealInducedPairNegativeOuterQuotient RealCharacterInducedSwap InductionStages

variable {d e : ComplexCharacterData} {k : ℕ}
  (hlink : IsLinkedAt d e k) (hneg : innerWeight d e k < 0)

def localEquiv : KFin 3 (lCD (x e) (rawOuter d e k)) ≃ₗ[ℂ]
    KFin 3 (lDC (x e) (rawOuter d e k)) :=
  RealVisibleInterlaced.equiv (x e) (rawOuter d e k) (interlacing_bounds hneg).1
    (interlacing_bounds hneg).2 (interlacing_gap hlink hneg)

theorem localEquiv_exact :
    IsRealStandardIntertwiner 3 (realStandardRep 3 (lDC (x e) (rawOuter d e k)))
      (realStandardLie 3 (lDC (x e) (rawOuter d e k)))
      (lCD (x e) (rawOuter d e k)) (localEquiv hlink hneg).toLinearMap := by
  have hm := RealVisibleInterlaced.equiv_exact (x e) (rawOuter d e k)
    (interlacing_bounds hneg).1 (interlacing_bounds hneg).2 (interlacing_gap hlink hneg)
  simpa only [LinearMap.id_comp, localEquiv] using
    hm.comp (isRealStandardIntertwiner_id 3 (lDC (x e) (rawOuter d e k))) bot_le

def expose : KF 4 (source d e k) ≃ₗ[ℂ] KF 4 (exposed d e k) :=
  standardEquivInd (n := 4) (a := 0) (r := 3)
    (ds := lCD (x e) (rawOuter d e k)) (es := lDC (x e) (rawOuter d e k))
    (pre := []) (post := [.character (v d e k)])
    (by decide : 0 + 3 ≤ 4) rfl rfl rfl rfl
    (localEquiv hlink hneg) (localEquiv_exact hlink hneg)

theorem expose_exact :
    IsRealIntertwinerModulo 4 (source d e k) (exposed d e k) ⊥
      (expose hlink hneg).toLinearMap :=
  modulo_of_standard (standardEquivInd_intertwiner (n := 4) (a := 0) (r := 3)
    (ds := lCD (x e) (rawOuter d e k)) (es := lDC (x e) (rawOuter d e k))
    (pre := []) (post := [.character (v d e k)])
    (by decide : 0 + 3 ≤ 4) rfl rfl rfl rfl
    (localEquiv hlink hneg) (localEquiv_exact hlink hneg))

abbrev sourceSlice (κ : unitaryCompact ℝ 4) :
    KF 4 (source d e k) →ₗ[ℂ] KFin 3 (lCD (x e) (rawOuter d e k)) :=
  sliceK (n := 4) (a := 0) (r := 3) (pre := [])
    (ds := lCD (x e) (rawOuter d e k)) (post := [.character (v d e k)])
    (by decide : 0 + 3 ≤ 4) rfl rfl κ

abbrev exposedSlice (κ : unitaryCompact ℝ 4) :
    KF 4 (exposed d e k) →ₗ[ℂ] KFin 3 (lDC (x e) (rawOuter d e k)) :=
  sliceK (n := 4) (a := 0) (r := 3) (pre := [])
    (ds := lDC (x e) (rawOuter d e k)) (post := [.character (v d e k)])
    (by decide : 0 + 3 ≤ 4) rfl rfl κ

theorem expose_slice (κ : unitaryCompact ℝ 4) (f : KF 4 (source d e k)) :
    exposedSlice κ (expose hlink hneg f) = localEquiv hlink hneg (sourceSlice κ f) :=
  sliceK_standardEquivInd (n := 4) (a := 0) (r := 3)
    (ds := lCD (x e) (rawOuter d e k)) (es := lDC (x e) (rawOuter d e k))
    (pre := []) (post := [.character (v d e k)])
    (by decide : 0 + 3 ≤ 4) rfl rfl rfl rfl
    (localEquiv hlink hneg) (localEquiv_exact hlink hneg) κ f

theorem expose_symm_slice (κ : unitaryCompact ℝ 4) (f : KF 4 (exposed d e k)) :
    sourceSlice κ ((expose hlink hneg).symm f) =
      (localEquiv hlink hneg).symm (exposedSlice κ f) :=
  sliceK_standardEquivInd_symm (n := 4) (a := 0) (r := 3)
    (ds := lCD (x e) (rawOuter d e k)) (es := lDC (x e) (rawOuter d e k))
    (pre := []) (post := [.character (v d e k)])
    (by decide : 0 + 3 ≤ 4) rfl rfl rfl rfl
    (localEquiv hlink hneg) (localEquiv_exact hlink hneg) κ f

/-- Every compact slice retains the actual even-branch canonical word formula. -/
theorem expose_forward_formula
    (hp : (d.weight.natAbs - (innerWeight d e k).natAbs) % 2 = 0) :
    ∃ (hB0 : RealVisibleInterlaced.SecondTailData (x e) (rawOuter d e k)
        (d.weight.natAbs - (innerWeight d e k).natAbs))
      (hB1 : RealVisibleInterlaced.SecondGenericData (x e) (rawOuter d e k)
        (d.weight.natAbs - (innerWeight d e k).natAbs)),
      ∀ κ f, (exposedSlice κ (expose hlink hneg f) : Langlands.GeneralLinear 3 ℝ → ℂ) =
        blockFrobMap hB1 (blockFrobMap hB0 (sourceSlice κ f)) := by
  have hp' : (d.weight.natAbs - (innerWeight d e k).natAbs + (x e).parity.val) % 2 = 0 := by
    simpa only [x, RealInducedPairQuotientPresentation.lo, RealJacquetFrobenius.charData,
      Fin.val_zero, add_zero] using hp
  obtain ⟨hB0, hB1, hf⟩ := RealVisibleInterlaced.equiv_forward_formula (x e) (rawOuter d e k)
    (interlacing_bounds hneg).1 (interlacing_bounds hneg).2 (interlacing_gap hlink hneg) hp'
  refine ⟨hB0, hB1, fun κ f => ?_⟩
  rw [expose_slice]
  exact hf _

/-- Every compact slice retains the actual odd-branch inverse word formula. -/
theorem expose_inverse_formula
    (hp : (d.weight.natAbs - (innerWeight d e k).natAbs) % 2 = 1) :
    ∃ (hA1 : RealVisibleInterlaced.FirstTailData (x e) (rawOuter d e k)
        (d.weight.natAbs - (innerWeight d e k).natAbs))
      (hA0 : RealVisibleInterlaced.FirstGenericData (x e) (rawOuter d e k)
        (d.weight.natAbs - (innerWeight d e k).natAbs)),
      ∀ κ f, (sourceSlice κ ((expose hlink hneg).symm f) : Langlands.GeneralLinear 3 ℝ → ℂ) =
        blockFrobMap hA0 (blockFrobMap hA1 (exposedSlice κ f)) := by
  have hp' : (d.weight.natAbs - (innerWeight d e k).natAbs + (x e).parity.val) % 2 = 1 := by
    simpa only [x, RealInducedPairQuotientPresentation.lo, RealJacquetFrobenius.charData,
      Fin.val_zero, add_zero] using hp
  obtain ⟨hA1, hA0, hf⟩ := RealVisibleInterlaced.equiv_inverse_formula (x e) (rawOuter d e k)
    (interlacing_bounds hneg).1 (interlacing_bounds hneg).2 (interlacing_gap hlink hneg) hp'
  refine ⟨hA1, hA0, fun κ f => ?_⟩
  rw [expose_symm_slice]
  exact hf _

/-- The same actual heavier replacement quotient, with this formula-visible exposing map. -/
def quotient : KF 4 (source d e k) →ₗ[ℂ] KF 4 (replacementPair d e k) :=
  (ofEqMap (kf_fused d e k)).comp
    ((blockFrobMap (innerTailData hlink hneg)).comp (expose hlink hneg).toLinearMap)

theorem quotient_exact :
    IsRealIntertwinerModulo 4 (source d e k) (replacementPair d e k) ⊥
      (quotient hlink hneg) :=
  modulo_comp_bot (modulo_ofEqMap (kf_fused d e k))
    (modulo_comp_bot
      (RealInducedPairQuotientPresentation.tail_exact (n := 4)
        (pre := [.induced (rawOuter d e k)]) (post := []) rfl
        (cutoff_bounds hneg).1 RealInducedPairNegativeInnerFiltration.tail_parity
        (middle_gap hlink hneg))
      (expose_exact hlink hneg))

theorem quotient_surjective : Function.Surjective (quotient hlink hneg) := by
  have htail : Function.Surjective (blockFrobMap (innerTailData hlink hneg)) := by
    intro f
    refine ⟨blockFrobMap (innerSectionData hlink hneg) f, ?_⟩
    exact RealCharacterInducedPushforward.tail_inv (cutoff_bounds hneg).1 (pairParity_eq _ _)
      RealInducedPairNegativeInnerFiltration.tail_parity (neg_one_pow_sq_fin _)
      (innerTailData hlink hneg) (innerSectionData hlink hneg) rfl
      (by simp only [RealCharacterPair.pairInduced_weight, Int.abs_eq_natAbs,
        Int.natAbs_natCast]) f
  exact (ofEqMap_surjective (kf_fused d e k)).comp
    (htail.comp (expose hlink hneg).surjective)

theorem ker_quotient :
    LinearMap.ker (quotient hlink hneg) =
      (LinearMap.range (blockFrobMap (innerBinomialData (d := d) (e := e) (k := k)))).comap
        (expose hlink hneg).toLinearMap := by
  unfold quotient
  rw [RealInducedPairOuterTail.ker_ofEqMap_comp, LinearMap.ker_comp]
  rw [RealInducedPairQuotientPresentation.ker_tail_eq_range
    (cutoff_bounds hneg).1 (pairParity_eq _ _)
    RealInducedPairNegativeInnerFiltration.tail_parity (neg_one_pow_sq_fin _)
    (innerBinomialData (d := d) (e := e) (k := k))
    (innerInverseBinomialData (d := d) (e := e) (k := k)) (innerTailData hlink hneg)]

/-- Both actual slice formulas, with their exact parity branches retained. -/
def HasSliceFormula : Prop :=
  ((d.weight.natAbs - (innerWeight d e k).natAbs) % 2 = 0 →
    ∃ (hB0 : RealVisibleInterlaced.SecondTailData (x e) (rawOuter d e k)
        (d.weight.natAbs - (innerWeight d e k).natAbs))
      (hB1 : RealVisibleInterlaced.SecondGenericData (x e) (rawOuter d e k)
        (d.weight.natAbs - (innerWeight d e k).natAbs)),
      ∀ κ f, (exposedSlice κ (expose hlink hneg f) : Langlands.GeneralLinear 3 ℝ → ℂ) =
        blockFrobMap hB1 (blockFrobMap hB0 (sourceSlice κ f))) ∧
  ((d.weight.natAbs - (innerWeight d e k).natAbs) % 2 = 1 →
    ∃ (hA1 : RealVisibleInterlaced.FirstTailData (x e) (rawOuter d e k)
        (d.weight.natAbs - (innerWeight d e k).natAbs))
      (hA0 : RealVisibleInterlaced.FirstGenericData (x e) (rawOuter d e k)
        (d.weight.natAbs - (innerWeight d e k).natAbs)),
      ∀ κ f, (sourceSlice κ ((expose hlink hneg).symm f) : Langlands.GeneralLinear 3 ℝ → ℂ) =
        blockFrobMap hA0 (blockFrobMap hA1 (exposedSlice κ f)))

theorem hasSliceFormula : HasSliceFormula hlink hneg :=
  ⟨expose_forward_formula hlink hneg, expose_inverse_formula hlink hneg⟩

end RealInducedPairVisibleOuterQuotient

/-- The actual negative outer replacement quotient is exact and onto with a
pulled-back binomial kernel and actual two-Frobenius formulas on compact slices. -/
def RealInducedPairVisibleOuterQuotientStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ)
    (hlink : RealInducedPairLinkedReplacement.IsLinkedAt d e k)
    (hneg : RealInducedPairLinkedReplacement.innerWeight d e k < 0),
    IsRealIntertwinerModulo 4 (RealInducedPairNegativeOuterQuotient.source d e k)
      (RealInducedPairLinkedReplacement.replacementPair d e k) ⊥
      (RealInducedPairVisibleOuterQuotient.quotient hlink hneg) ∧
    Function.Surjective (RealInducedPairVisibleOuterQuotient.quotient hlink hneg) ∧
    LinearMap.ker (RealInducedPairVisibleOuterQuotient.quotient hlink hneg) =
      (LinearMap.range (RealBlockFrobeniusMap.blockFrobMap
        (RealInducedPairNegativeOuterQuotient.innerBinomialData (d := d) (e := e) (k := k)))).comap
          (RealInducedPairVisibleOuterQuotient.expose hlink hneg).toLinearMap ∧
    RealInducedPairVisibleOuterQuotient.HasSliceFormula hlink hneg

theorem realInducedPairVisibleOuterQuotient : RealInducedPairVisibleOuterQuotientStatement := by
  intro d e k hlink hneg
  exact ⟨RealInducedPairVisibleOuterQuotient.quotient_exact hlink hneg,
    RealInducedPairVisibleOuterQuotient.quotient_surjective hlink hneg,
    RealInducedPairVisibleOuterQuotient.ker_quotient hlink hneg,
    RealInducedPairVisibleOuterQuotient.hasSliceFormula hlink hneg⟩

end Langlands.Archimedean
