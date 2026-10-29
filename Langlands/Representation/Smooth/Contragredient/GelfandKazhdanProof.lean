import Langlands.Representation.Smooth.Contragredient.GelfandKazhdanAssembly
import Langlands.Representation.Character.SeparationProof
import Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof

/-!
# Proof of the Gelfand–Kazhdan realization of the smooth contragredient

The conditional character assembly receives the published character separation
theorem and the published transpose invariance of conjugation-invariant distributions
on the actual general linear group.
-/

namespace Langlands

universe uF uV

/-- Bernstein–Zelevinsky (1976), Theorem 7.3: an irreducible admissible representation
of `GL_(n+1)(F)`, composed with inverse transpose, is equivalent to its smooth dual. -/
theorem gelfandKazhdanContragredient : GelfandKazhdanContragredientStatement.{uF,uV} :=
  gelfandKazhdanContragredient_of_character_inputs characterSeparation
    generalLinearConjugationDistributionTranspose

end Langlands
