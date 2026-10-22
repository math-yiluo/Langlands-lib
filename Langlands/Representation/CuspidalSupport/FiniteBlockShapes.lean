import Langlands.Group.GL.Blocks
import Mathlib.Combinatorics.Enumerative.Composition

/-! Finite enumeration of the actual ordered positive block shapes. -/

namespace Langlands.GeneralLinear.BlockShape

variable {n : ℕ}

/-- The ordered list of positive block sizes, as a Mathlib composition. -/
def toComposition (B : BlockShape n) : Composition n where
  blocks := List.ofFn B.size
  blocks_pos := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact B.positive i
  blocks_sum := by
    simpa only [List.sum_ofFn] using B.sum_eq

theorem toComposition_injective :
    Function.Injective (toComposition (n := n)) := by
  rintro ⟨l, s, hp, hs⟩ ⟨l', s', hp', hs'⟩ h
  have hl := congrArg (fun c : Composition n => c.blocks.length) h
  simp only [toComposition, List.length_ofFn] at hl
  subst l'
  have he : s = s' := by
    apply List.ofFn_injective
    exact congrArg Composition.blocks h
  subst s'
  rfl

/-- There are finitely many ordered positive block shapes of any fixed rank. -/
instance finiteBlockShape : Finite (BlockShape n) :=
  Finite.of_injective toComposition toComposition_injective

end Langlands.GeneralLinear.BlockShape
