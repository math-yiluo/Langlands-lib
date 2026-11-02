import Langlands.Algebra.NonUnitalNonnilpotentLeftResolventProof
import Langlands.Algebra.NonUnitalLeftShiftSimpleQuotientProof

/-!
# Renard B.III: separation by the actual original-action quotient

Combine the original one-sided resolvent with the actual simple quotient,
then assemble the three unchanged components at arbitrary algebra universe.
-/

set_option autoImplicit false

universe uA

namespace Langlands.Renard

/-- Every original nonnilpotent element is separated by the actual class of `1`
in a simple quotient, with simplicity for all original stable additive subgroups. -/
theorem nonUnitalSeparation (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] :
    NonUnitalSeparationStatement A := by
  intro hrank a ha
  obtain ⟨z, hz, hleft⟩ := nonUnitalNonnilpotentLeftResolvent A hrank a ha
  obtain ⟨I, hI, _hspan, hsimple, hrestriction⟩ :=
    nonUnitalLeftShiftSimpleQuotient A a z hz hleft
  exact ⟨I, hI, hsimple, hrestriction⟩

/-- The exact closed conjunction of all three original nonunital targets. -/
theorem nonUnitalSeparationReduction : NonUnitalSeparationReductionStatement.{uA} := by
  intro A _ _ _ _
  exact ⟨nonUnitalNonnilpotentLeftResolvent A, nonUnitalLeftShiftSimpleQuotient A,
    nonUnitalSeparation A⟩

end Langlands.Renard
