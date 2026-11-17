import Langlands.Representation.Archimedean.RealStandardEquivStages
import Langlands.Representation.Archimedean.RealCharacterInducedInterlaced
import Langlands.Representation.Archimedean.RealInducedPairLinkedReplacement
import Langlands.Representation.Archimedean.RealInducedPairFrobenius

/-! # Reordering the actual mixed outer target at a linked pair -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealInducedPairOuterReorder

open InductionStages RealInducedPairLinkedReplacement RealInducedPairFrobenius
open RealCharacterInducedSwap RealCharacterInducedInterlaced

variable (d e : ComplexCharacterData) (k : ℕ)

abbrev mixedList : List RealBlock :=
  [.character (first d), .induced (outerData d e k), .character (second e)]

/-- The two remaining inner characters are adjacent in this list. -/
abbrev reorderedList : List RealBlock :=
  [.induced (outerData d e k), .character (first d), .character (second e)]

theorem interlacing_upper : d.weight.natAbs < (outerData d e k).weight.natAbs := by
  simp only [outerData, characterOfParams_weight, Int.natAbs_natCast]
  have hd := le_max_left d.weight.natAbs e.weight.natAbs
  unfold outerWeight
  omega

variable {d e k}

/-- The first endpoint of the first block is above the lower outer endpoint by
exactly the first block's absolute weight. -/
theorem interlacing_gap (h : IsLinkedAt d e k) :
    (chB (outerData d e k)).exponent - (first d).exponent =
      -(d.weight.natAbs : ℂ) := by
  have hb := (endpoint_equalities h).2.1
  simp only [chB_exponent, outerData, characterOfParams_exponent,
    characterOfParams_weight, Int.natAbs_natCast]
  change outerExponent d e - (outerWeight d e k : ℂ) / 2 -
    (d.exponent + (d.weight.natAbs : ℂ) / 2) = _
  linear_combination hb

variable (h : IsLinkedAt d e k) (hd : 0 < d.weight.natAbs)

/-- The actual GL3 interlaced equivalence moving the first inner character past
the outer block. -/
def middleEquiv :
    KFin 3 (lCD (first d) (outerData d e k)) ≃ₗ[ℂ]
      KFin 3 (lDC (first d) (outerData d e k)) :=
  interlacedEquiv (first d) (outerData d e k) hd (interlacing_upper d e k)
    (interlacing_gap h)

theorem middleEquiv_intertwiner :
    IsRealStandardIntertwiner 3
      (realStandardRep 3 (lDC (first d) (outerData d e k)))
      (realStandardLie 3 (lDC (first d) (outerData d e k)))
      (lCD (first d) (outerData d e k)) (middleEquiv h hd).toLinearMap :=
  interlacedEquiv_isIntertwiner (first d) (outerData d e k)
    hd (interlacing_upper d e k) (interlacing_gap h)

/-- The actual mixed GL4 target can be reordered, with the last character retained. -/
def reorderEquiv : KFin 4 (mixedList d e k) ≃ₗ[ℂ] KFin 4 (reorderedList d e k) :=
  standardEquivInd (n := 4) (a := 0) (r := 3)
    (ds := lCD (first d) (outerData d e k))
    (es := lDC (first d) (outerData d e k))
    (pre := []) (post := [.character (second e)])
    (by decide : 0 + 3 ≤ 4) rfl rfl rfl rfl
    (middleEquiv h hd) (middleEquiv_intertwiner h hd)

theorem reorderEquiv_intertwiner :
    IsRealStandardIntertwiner 4 (realStandardRep 4 (reorderedList d e k))
      (realStandardLie 4 (reorderedList d e k)) (mixedList d e k)
      (reorderEquiv h hd).toLinearMap :=
  standardEquivInd_intertwiner (n := 4) (a := 0) (r := 3)
    (ds := lCD (first d) (outerData d e k))
    (es := lDC (first d) (outerData d e k))
    (pre := []) (post := [.character (second e)])
    (by decide : 0 + 3 ≤ 4) rfl rfl rfl rfl
    (middleEquiv h hd) (middleEquiv_intertwiner h hd)

theorem reorderEquiv_symm_intertwiner :
    IsRealStandardIntertwiner 4 (realStandardRep 4 (mixedList d e k))
      (realStandardLie 4 (mixedList d e k)) (reorderedList d e k)
      (reorderEquiv h hd).symm.toLinearMap :=
  standardEquivInd_symm_intertwiner (n := 4) (a := 0) (r := 3)
    (ds := lCD (first d) (outerData d e k))
    (es := lDC (first d) (outerData d e k))
    (pre := []) (post := [.character (second e)])
    (by decide : 0 + 3 ≤ 4) rfl rfl rfl rfl
    (middleEquiv h hd) (middleEquiv_intertwiner h hd)

end RealInducedPairOuterReorder

open InductionStages RealInducedPairLinkedReplacement RealInducedPairOuterReorder

/-- At a linked pair with positive first weight, the mixed outer target has an
actual exact equivalence exposing the two inner characters as adjacent blocks. -/
def RealInducedPairOuterReorderStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ) (_h : IsLinkedAt d e k)
    (_hd : 0 < d.weight.natAbs),
    ∃ E : KFin 4 (mixedList d e k) ≃ₗ[ℂ] KFin 4 (reorderedList d e k),
      IsRealStandardIntertwiner 4 (realStandardRep 4 (reorderedList d e k))
        (realStandardLie 4 (reorderedList d e k)) (mixedList d e k) E.toLinearMap ∧
      IsRealStandardIntertwiner 4 (realStandardRep 4 (mixedList d e k))
        (realStandardLie 4 (mixedList d e k)) (reorderedList d e k) E.symm.toLinearMap

theorem realInducedPairOuterReorder : RealInducedPairOuterReorderStatement := by
  intro d e k h hd
  exact ⟨reorderEquiv h hd, reorderEquiv_intertwiner h hd,
    reorderEquiv_symm_intertwiner h hd⟩

end Langlands.Archimedean
