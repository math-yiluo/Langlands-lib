import Langlands.GroupScheme.Rational.ParabolicSplitComponentLeviProof
import Langlands.GroupScheme.Rational.LeviSplitComponentRadicalProof
import Langlands.GroupScheme.Rational.ParabolicSplitComponentConjugacyProof
import Langlands.GroupScheme.Rational.LeviCentralizerCharacterizationProof
import Langlands.GroupScheme.Rational.MinimalParabolicSplitComponentProof

/-!
# Split components of parabolic subgroups (Renard V.3.1–V.3.2): the assembled statement

This module proves the conjunction `ParabolicSplitComponentStatements` by pairing the five
published component proofs.
-/

namespace Langlands.GroupScheme

universe u

/-- The five split-component assertions of Renard V.3.1 and the first sentence of V.3.2, as
stated in `ParabolicSplitComponentStatements`, assembled from their published proofs. -/
theorem parabolicSplitComponents : ParabolicSplitComponentStatements.{u} :=
  ⟨parabolicSplitComponentLevi, leviSplitComponentRadical, parabolicSplitComponentConjugacy,
    leviCentralizerCharacterization, minimalParabolicSplitComponent⟩

end Langlands.GroupScheme
