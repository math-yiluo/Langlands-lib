import Langlands.ClassFieldTheory.Local.FiniteCupArtinComparisonStatement

/-!
# Failure of the arithmetic inverse-cup character comparison
-/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- The arithmetic inverse-cup character comparison fails: it is not the case
that arithmetic inverse cup has the positive carry-symbol character values for
every finite Galois extension in universe `u`. -/
def FiniteCupArtinCharacterComparisonFails : Prop :=
  ¬ FiniteCupArtinCharacterComparison.{u}

end Langlands.ClassFieldTheory.Local
