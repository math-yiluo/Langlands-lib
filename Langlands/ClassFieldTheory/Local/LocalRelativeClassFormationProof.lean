import Langlands.ClassFieldTheory.Local.ClassFormationStatement
import Langlands.ClassFieldTheory.Local.ClassFormationAbsoluteCorestrictionProof

/-! # Local relative class formation

The simultaneous local class formation supplies a single invariant family
with all the finite relative properties required here.
-/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- The finite relative properties of simultaneous local class formation,
for every prime and an arbitrary carrier universe. -/
theorem localRelativeClassFormation :
    LocalRelativeClassFormationStatement.{u} := by
  intro p _
  obtain ⟨I, hArithmetic, _, hRelative, hConjugacy, hCorestriction,
    hFundamental, hInflation, hRestriction, hFundamentalCorestriction,
    hFundamentalConjugacy, _⟩ :=
    localAbsoluteCorestrictionCompatibleClassFormation.{u} p
  exact ⟨I, hArithmetic, hRelative, hConjugacy, hCorestriction,
    hFundamental, hInflation, hRestriction, hFundamentalCorestriction,
    hFundamentalConjugacy⟩

end Langlands.ClassFieldTheory.Local
