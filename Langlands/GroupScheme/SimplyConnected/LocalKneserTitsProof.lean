import Langlands.GroupScheme.SimplyConnected.LocalKneserTitsStatement
import Langlands.GroupScheme.SimplyConnected.LocalRankOneClassificationReduction
import Langlands.GroupScheme.SimplyConnected.RankOneLeviFactorExistenceProof
import Langlands.GroupScheme.SimplyConnected.RankOneLeviDerivedGenerationProof
import Langlands.GroupScheme.SimplyConnected.RankOneLeviCocenterGenerationProof
import Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingProof
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleWeilRestrictionProof
import Langlands.GroupScheme.Rational.AffineWeilSplitRankProof
import Langlands.GroupScheme.Rational.AffineWeilParabolicElementaryProof
import Langlands.GroupScheme.SimplyConnected.LocalRankOneClassificationProof
import Langlands.GroupScheme.Quaternionic.LocalSymplecticKneserTitsProof
import Langlands.GroupScheme.Quaternionic.LocalSpinKneserTitsProof

/-! # Local Kneser–Tits in terms of rational parabolic radicals: proof -/

universe u

namespace Langlands.GroupScheme

/-- **Local Kneser–Tits.** Over every nonarchimedean local field, a normal subgroup of the
rational points of an isotropic almost-simple simply connected group which contains the
rational points of the unipotent radicals of all rational parabolic subgroups is the whole
group (Prasad–Raghunathan 1985). -/
theorem localKneserTits : LocalKneserTitsStatement.{u} :=
  localKneserTits_of_rankOneLeviFactors_of_classification
    ⟨rankOneLeviFactorExistence, rankOneLeviDerivedGeneration, rankOneLeviCocenterGeneration⟩
    localSimplyConnectedCocycleVanishing simplyConnectedAlmostSimpleWeilRestriction
    affineWeilSplitRank affineWeilParabolicElementarySubgroup
    ⟨localRankOneClassification, Quaternionic.localSymplecticKneserTits,
      Quaternionic.localSpinKneserTits⟩

end Langlands.GroupScheme
