import Langlands.GroupScheme.RelativeLevi.ConjugacySynthesis
import Langlands.GroupScheme.Torus.EtaleLocalMaximalExistenceProof
import Langlands.GroupScheme.Torus.EtaleLocalMaximalConjugacyProof
import Langlands.GroupScheme.RelativeLevi.TorusLeviProof
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalProof
import Langlands.GroupScheme.RelativeLevi.SelfNormalizerProof

/-! # Unique conjugacy of relative Levi subgroups by the unipotent radical -/

universe u

namespace Langlands.GroupScheme

/-- Any two relative Levi subgroups of a parabolic are conjugate by a unique
global point of its unipotent radical, over an arbitrary base scheme. -/
theorem relativeLeviConjugacy : RelativeLeviConjugacyStatement.{u} :=
  RelativeLevi.relativeLeviConjugacy_of_structuralStatements
    etaleLocalMaximalTorusExistence etaleLocalMaximalTorusConjugacy
    relativeTorusLevi relativeUnipotentRadical relativeLeviSelfNormalizer

end Langlands.GroupScheme
