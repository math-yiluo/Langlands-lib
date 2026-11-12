import Langlands.Representation.Plancherel.SplitComponentLatticeBridge
import Langlands.GroupScheme.Rational.CharacterRestrictionProof

/-! # Finite index and uniformizer realization of the split-component valuation image

The published reduction `splitComponentLatticeStatement_of_characterRestriction` derives both
conjuncts of `SplitComponentLatticeStatement` from the character restriction statement, which is
proved unconditionally by `Langlands.GroupScheme.characterRestriction`.
-/

universe u

namespace Langlands.Plancherel.RenardCartan

/-- For every actual connected reductive group over a nonarchimedean local field and every actual
split component `s`, the image of the split-torus points has finite index in the actual
character-valuation image, and valuation is a bijection from `C0` onto that image. -/
theorem splitComponentLattice : SplitComponentLatticeStatement.{u} :=
  splitComponentLatticeStatement_of_characterRestriction Langlands.GroupScheme.characterRestriction

end Langlands.Plancherel.RenardCartan
