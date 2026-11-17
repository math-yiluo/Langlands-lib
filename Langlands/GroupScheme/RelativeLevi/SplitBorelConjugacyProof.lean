import Langlands.GroupScheme.RelativeLevi.SplitBorelConjugacyReduction
import Langlands.GroupScheme.RelativeLevi.SplitBorelVectorSeriesProof
import Langlands.GroupScheme.Reductive.SplitNormalizerLocalLiftingProof

/-! # Zariski-local conjugacy of Borel subgroups of a split reductive group -/

universe u

namespace Langlands.GroupScheme

/-- The full split Borel Zariski-local conjugacy statement over every
commutative ring, with exactly the published splitting hypotheses. -/
theorem splitBorelZariskiLocalConjugacy :
    SplitBorelZariskiLocalConjugacyStatement.{u} :=
  splitBorelZariskiLocalConjugacy_of_structure_and_lifting
    splitBorelVectorSeries.{u} splitNormalizerGeometricLocalLifting.{u}

end Langlands.GroupScheme
