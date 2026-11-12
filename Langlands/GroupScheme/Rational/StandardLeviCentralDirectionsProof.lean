import Langlands.GroupScheme.Rational.StandardLeviCentralDirectionsAssembly
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.CharacterRestrictionProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Dynamic.LieProof

/-! # Proof: standard-Levi split components realize selected-root annihilators -/

universe u

namespace Langlands.GroupScheme

/-- **Standard-Levi central directions** over arbitrary fields: selected simple
roots cut out a real cocharacter subspace of the expected codimension, and every
split component of every closed representative of the standard Levi embeds into
the maximal split torus with exactly that image. -/
theorem standardLeviCentralDirections : StandardLeviCentralDirectionsStatement.{u} :=
  standardLeviCentralDirections_of_standard_dynamic_characterRestriction
    standardCocharacter dynamicCentralizerReductive dynamicLie characterRestriction

end Langlands.GroupScheme
