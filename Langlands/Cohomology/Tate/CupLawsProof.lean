import Langlands.Cohomology.Tate.CupStatement
import Langlands.Cohomology.Tate.CupBoundarySecond
import Langlands.Cohomology.Tate.CupTransfer

universe u

namespace Langlands.Tate

/-- The constructed Tate cup satisfies the exact normalization and compatibility laws. -/
theorem cupLaws : CupLaws.{u} := by
  intro R G _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B C φ
    exact cup_zero_zero φ
  · intro A B C φ a b
    exact cup_zeroClass φ a b
  · intro A A' B B' C C' φ φ' f g h hφ p q a b
    exact cup_naturality p q φ φ' f g h hφ a b
  · intro S hS B hB p q x b
    exact tensorCup_delta_first S hS B hB p q x b
  · intro S hS A hA p q a b
    exact tensorCup_delta_second S hS A hA p q a b
  · intro H _ _ A B C φ p q
    exact ⟨cup_restriction H φ p q, cup_corestriction H φ p q⟩

end Langlands.Tate
