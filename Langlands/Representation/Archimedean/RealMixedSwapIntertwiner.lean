import Langlands.Representation.Archimedean.RealMixedSwapConjugation
import Langlands.Representation.Archimedean.RealMixedSwapStandard
import Langlands.Representation.Archimedean.RealCharacterInducedUnlinked

/-! # The induced-character rank-three unlinked intertwiner -/

noncomputable section

namespace Langlands.Archimedean.RealMixedSwapTwist

open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Conjugation of a reversed character-induced map by the mixed signed equivalences. -/
def inducedCharacterSwapMap (d : ComplexCharacterData) (b : RealCharacterData)
    (T : kFiniteFunctions
        (realStandardModule 3 [.character (reverseCharacter d b), .induced (reverseInduced d)])
        (unitaryCompact ℝ 3) →ₗ[ℂ]
      kFiniteFunctions
        (realStandardModule 3 [.induced (reverseInduced d), .character (reverseCharacter d b)])
        (unitaryCompact ℝ 3)) :
    kFiniteFunctions (realStandardModule 3 [.induced d, .character b]) (unitaryCompact ℝ 3)
      →ₗ[ℂ] kFiniteFunctions (realStandardModule 3 [.character b, .induced d])
        (unitaryCompact ℝ 3) :=
  conjugateMap (inducedCharacterSignedEquiv d b) (characterInducedSignedEquiv d b) T

theorem inducedCharacterSwapMap_intertwiner (d : ComplexCharacterData) (b : RealCharacterData)
    {T : kFiniteFunctions
        (realStandardModule 3 [.character (reverseCharacter d b), .induced (reverseInduced d)])
        (unitaryCompact ℝ 3) →ₗ[ℂ]
      kFiniteFunctions
        (realStandardModule 3 [.induced (reverseInduced d), .character (reverseCharacter d b)])
        (unitaryCompact ℝ 3)}
    (hT : IsRealStandardIntertwiner 3
      (realStandardRep 3 [.induced (reverseInduced d), .character (reverseCharacter d b)])
      (realStandardLie 3 [.induced (reverseInduced d), .character (reverseCharacter d b)])
      [.character (reverseCharacter d b), .induced (reverseInduced d)] T) :
    IsRealStandardIntertwiner 3
      (realStandardRep 3 [.character b, .induced d])
      (realStandardLie 3 [.character b, .induced d])
      [.induced d, .character b] (inducedCharacterSwapMap d b T) :=
  isRealStandardIntertwiner_conjugateMap (mixedSignPower d)
    (inducedCharacterSignedEquiv d b) (characterInducedSignedEquiv d b)
    (inducedCharacterSignedEquiv_apply_coe d b)
    (characterInducedSignedEquiv_apply_coe d b) hT

theorem inducedCharacterSwapMap_injective (d : ComplexCharacterData) (b : RealCharacterData)
    {T : kFiniteFunctions
        (realStandardModule 3 [.character (reverseCharacter d b), .induced (reverseInduced d)])
        (unitaryCompact ℝ 3) →ₗ[ℂ]
      kFiniteFunctions
        (realStandardModule 3 [.induced (reverseInduced d), .character (reverseCharacter d b)])
        (unitaryCompact ℝ 3)}
    (hT : Function.Injective T) :
    Function.Injective (inducedCharacterSwapMap d b T) :=
  (characterInducedSignedEquiv d b).symm.injective.comp
    (hT.comp (inducedCharacterSignedEquiv d b).injective)

/-- The reversed character-induced existence transports to the original mixed order. -/
theorem inducedCharacterSwap_exists (d : ComplexCharacterData) (b : RealCharacterData)
    (h : RealInjectiveIntertwinerExists 3
      [.character (reverseCharacter d b), .induced (reverseInduced d)]
      [.induced (reverseInduced d), .character (reverseCharacter d b)]) :
    RealInjectiveIntertwinerExists 3 [.induced d, .character b] [.character b, .induced d] := by
  obtain ⟨T, hTi, hT⟩ := h
  exact ⟨inducedCharacterSwapMap d b T, inducedCharacterSwapMap_injective d b hTi,
    inducedCharacterSwapMap_intertwiner d b hT⟩

/-- The unconditional GL3 induced-character unlinked swap with its original hypotheses. -/
theorem inducedCharacterSwap_unlinked (d : ComplexCharacterData) (b : RealCharacterData)
    (hd : d.weight ≠ 0)
    (hord : realBlockExponent (.character b) ≤ realBlockExponent (.induced d))
    (hun : AreRealBlocksUnlinked (.induced d) (.character b)) :
    RealInjectiveIntertwinerExists 3 [.induced d, .character b] [.character b, .induced d] := by
  apply inducedCharacterSwap_exists d b
  have h := RealCharacterInducedUnlinked.injective_unlinked
    (reverseCharacter d b) (reverseInduced d)
    (by simpa only [reverseInduced_weight] using hd)
    ((exponent_order_reverse d b).mpr hord) ((unlinked_reverse d b hd).mpr hun)
  simpa only [RealCharacterInducedSwap.lCD, RealCharacterInducedSwap.lDC] using h

end Langlands.Archimedean.RealMixedSwapTwist
