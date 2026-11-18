import Langlands.Representation.Archimedean.RealInducedPairNegativeOuterQuotient

/-! # An actual reversed-source generator of the outer replacement kernel -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealInducedPairNegativeOuterKernel

open RealStandardFiltration RealBlockFrobeniusMap RealCharacterPairReducible
open RealInducedPairLinkedReplacement RealInducedPairNegativeInnerQuotient
open RealInducedPairNegativeOuterQuotient
open RealCharacterInducedSwap RealCharacterInducedInterlaced InductionStages

variable (d e : ComplexCharacterData) (k : ℕ)

/-- Reverse the two remaining characters of the mixed outer source, retaining their signs. -/
abbrev companionSource : List RealBlock :=
  [.character (v d e k), .induced (rawOuter d e k), .character (x e)]

/-- The same source after moving its first character past the outer block. -/
abbrev companionExposed : List RealBlock :=
  [.induced (rawOuter d e k), .character (v d e k), .character (x e)]

variable {d e k} (hlink : IsLinkedAt d e k) (hneg : innerWeight d e k < 0)

include hneg in
theorem companion_bounds :
    0 < d.weight.natAbs ∧ d.weight.natAbs < (rawOuter d e k).weight.natAbs := by
  have hb := cutoff_bounds hneg
  have hm := le_max_left d.weight.natAbs e.weight.natAbs
  simp only [rawOuter, RealCharacterPair.pairInduced_weight, Int.natAbs_natCast]
  unfold outerWeight
  omega

include hlink in
theorem companion_gap :
    (chB (rawOuter d e k)).exponent - (v d e k).exponent = -(d.weight.natAbs : ℂ) := by
  have hP := (RealInducedPairDistantParity.differences
    (sd := leftParity d e k) (se := 0) hlink).1
  have hL := RealInducedPairQuotientPresentation.hi_sub_lo d (leftParity d e k)
  change (((u d e k).exponent + (y e).exponent) / 2 -
    (outerWeight d e k : ℂ) / 2) - (v d e k).exponent = _
  linear_combination hP / 2 - hL

def companionLocalEquiv :
    KFin 3 (lCD (v d e k) (rawOuter d e k)) ≃ₗ[ℂ]
      KFin 3 (lDC (v d e k) (rawOuter d e k)) :=
  interlacedEquiv (v d e k) (rawOuter d e k) (companion_bounds hneg).1
    (companion_bounds hneg).2 (companion_gap hlink)

theorem companionLocalEquiv_exact :
    IsRealStandardIntertwiner 3 (realStandardRep 3 (lDC (v d e k) (rawOuter d e k)))
      (realStandardLie 3 (lDC (v d e k) (rawOuter d e k)))
      (lCD (v d e k) (rawOuter d e k)) (companionLocalEquiv hlink hneg).toLinearMap :=
  interlacedEquiv_isIntertwiner (v d e k) (rawOuter d e k) (companion_bounds hneg).1
    (companion_bounds hneg).2 (companion_gap hlink)

/-- The actual equivalence exposing the descending inner pair in the companion source. -/
def companionEquiv : KF 4 (companionSource d e k) ≃ₗ[ℂ] KF 4 (companionExposed d e k) :=
  standardEquivInd (n := 4) (a := 0) (r := 3)
    (ds := lCD (v d e k) (rawOuter d e k)) (es := lDC (v d e k) (rawOuter d e k))
    (pre := []) (post := [.character (x e)])
    (by decide : 0 + 3 ≤ 4) rfl rfl rfl rfl
    (companionLocalEquiv hlink hneg) (companionLocalEquiv_exact hlink hneg)

theorem companionEquiv_exact :
    IsRealIntertwinerModulo 4 (companionSource d e k) (companionExposed d e k) ⊥
      (companionEquiv hlink hneg).toLinearMap :=
  RealInducedPairNegativeOuterQuotient.modulo_of_standard
    (standardEquivInd_intertwiner (n := 4) (a := 0) (r := 3)
      (ds := lCD (v d e k) (rawOuter d e k)) (es := lDC (v d e k) (rawOuter d e k))
      (pre := []) (post := [.character (x e)])
      (by decide : 0 + 3 ≤ 4) rfl rfl rfl rfl
      (companionLocalEquiv hlink hneg) (companionLocalEquiv_exact hlink hneg))

theorem exposeEquiv_symm_exact :
    IsRealIntertwinerModulo 4 (exposed d e k) (source d e k) ⊥
      (exposeEquiv hlink hneg).symm.toLinearMap :=
  modulo_of_comp_surjective (modulo_id _) (exposeEquiv_exact hlink hneg)
    (exposeEquiv hlink hneg).surjective
    (LinearMap.ext fun f => (exposeEquiv hlink hneg).symm_apply_apply f)

/-- Reorder, apply the inner binomial, and undo the original source reordering. -/
def kernelGenerator : KF 4 (companionSource d e k) →ₗ[ℂ] KF 4 (source d e k) :=
  (exposeEquiv hlink hneg).symm.toLinearMap.comp
    ((blockFrobMap (innerBinomialData (d := d) (e := e) (k := k))).comp
      (companionEquiv hlink hneg).toLinearMap)

theorem kernelGenerator_exact :
    IsRealIntertwinerModulo 4 (companionSource d e k) (source d e k) ⊥
      (kernelGenerator hlink hneg) :=
  modulo_comp_bot (exposeEquiv_symm_exact hlink hneg)
    (modulo_comp_bot
      (RealInducedPairQuotientPresentation.binomial_exact (n := 4)
        (pre := [.induced (rawOuter d e k)]) (post := []) rfl
        (cutoff_bounds hneg).1 RealInducedPairNegativeInnerFiltration.tail_parity
        (middle_gap hlink hneg))
      (companionEquiv_exact hlink hneg))

/-- The reversed-source map has exactly the actual replacement quotient kernel as its range. -/
theorem range_kernelGenerator :
    LinearMap.range (kernelGenerator hlink hneg) =
      LinearMap.ker (replacementQuotient hlink hneg) := by
  rw [ker_replacementQuotient hlink hneg]
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    change exposeEquiv hlink hneg
      ((exposeEquiv hlink hneg).symm
        (blockFrobMap innerBinomialData (companionEquiv hlink hneg f))) ∈
      LinearMap.range (blockFrobMap innerBinomialData)
    rw [LinearEquiv.apply_symm_apply]
    exact ⟨companionEquiv hlink hneg f, rfl⟩
  · intro f hf
    obtain ⟨z, hz⟩ := hf
    refine ⟨(companionEquiv hlink hneg).symm z, ?_⟩
    apply (exposeEquiv hlink hneg).injective
    change exposeEquiv hlink hneg
      ((exposeEquiv hlink hneg).symm
        (blockFrobMap innerBinomialData
          (companionEquiv hlink hneg ((companionEquiv hlink hneg).symm z)))) =
      exposeEquiv hlink hneg f
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hz

theorem replacementQuotient_comp_kernelGenerator :
    (replacementQuotient hlink hneg).comp (kernelGenerator hlink hneg) = 0 := by
  apply LinearMap.ext
  intro f
  have hf : kernelGenerator hlink hneg f ∈
      LinearMap.ker (replacementQuotient hlink hneg) := by
    rw [← range_kernelGenerator hlink hneg]
    exact ⟨f, rfl⟩
  exact hf

end RealInducedPairNegativeOuterKernel

/-- The mixed outer replacement quotient has an exact kernel presentation from the source
with its two remaining characters reversed and their actual parities retained. -/
def RealInducedPairNegativeOuterKernelStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ)
    (hlink : RealInducedPairLinkedReplacement.IsLinkedAt d e k)
    (hneg : RealInducedPairLinkedReplacement.innerWeight d e k < 0),
    ∃ K : RealStandardFiltration.KF 4
        (RealInducedPairNegativeOuterKernel.companionSource d e k) →ₗ[ℂ]
      RealStandardFiltration.KF 4 (RealInducedPairNegativeOuterQuotient.source d e k),
      IsRealIntertwinerModulo 4 (RealInducedPairNegativeOuterKernel.companionSource d e k)
        (RealInducedPairNegativeOuterQuotient.source d e k) ⊥ K ∧
      LinearMap.range K = LinearMap.ker
        (RealInducedPairNegativeOuterQuotient.replacementQuotient hlink hneg)

theorem realInducedPairNegativeOuterKernel : RealInducedPairNegativeOuterKernelStatement :=
  fun _ _ _ hlink hneg =>
    ⟨RealInducedPairNegativeOuterKernel.kernelGenerator hlink hneg,
      RealInducedPairNegativeOuterKernel.kernelGenerator_exact hlink hneg,
      RealInducedPairNegativeOuterKernel.range_kernelGenerator hlink hneg⟩

end Langlands.Archimedean
