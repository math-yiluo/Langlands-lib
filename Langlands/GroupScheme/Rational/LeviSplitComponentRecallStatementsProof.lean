import Langlands.GroupScheme.Rational.LeviSplitComponentCentralizerProof
import Langlands.GroupScheme.Rational.LeviSplitComponentNormalizerProof
import Langlands.GroupScheme.Rational.LeviParabolicFiniteProof

/-! # Assembly of the three Levi split-component recall assertions -/

universe u

namespace Langlands.GroupScheme

/-- The centralizer, rational normalizer, and finiteness assertions recalled
in Renard V.3.1 and V.3.5.1, assembled from their published proofs. -/
theorem leviSplitComponentRecall : LeviSplitComponentRecallStatements.{u} :=
  ⟨leviSplitComponentCentralizer.{u}, leviSplitComponentNormalizer.{u},
    leviParabolicFinite.{u}⟩

end Langlands.GroupScheme
