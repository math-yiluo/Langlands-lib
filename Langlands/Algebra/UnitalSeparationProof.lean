import Langlands.Algebra.LeftShiftSimpleQuotientProof
import Langlands.Algebra.NonnilpotentLeftResolventProof

/-!
# Renard B.III: the unital separation lemma

Combine the published one-sided resolvent theorem with the actual
maximal-left-ideal/simple-quotient argument, retaining the class of `1`.
-/

universe u

namespace Langlands.Renard

/-- Renard B.III in a unital complex algebra: every nonnilpotent element in
countable dimension moves the class of `1` in some simple left quotient. -/
theorem unitalSeparation (A : Type u) [Ring A] [Algebra ℂ A] :
    UnitalSeparationStatement A := by
  intro hrank a ha
  obtain ⟨z, hz, hleft⟩ := nonnilpotentLeftResolvent A hrank a ha
  obtain ⟨I, hI, _, hsimple, hsep⟩ := leftShiftSimpleQuotient A a z hz hleft
  exact ⟨I, hI, hsimple, hsep⟩

end Langlands.Renard
