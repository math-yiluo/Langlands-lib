import Langlands.Representation.Aubert.General.RationalReductiveUnimodularityProof
import Langlands.Representation.Aubert.General.RationalInductionDualityAssembly
import Langlands.Representation.Aubert.General.RationalLeviUnimodularityReduction
import Langlands.BruhatTits.Parabolic.QuotientCompactProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Natural same-parabolic induction duality on the actual rational-point group -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- **Natural induction duality.** For every connected reductive group over a
nonarchimedean local field, normalized induction from an actual standard parabolic commutes,
naturally in admissible inducing objects, with the smooth contragredient. -/
theorem rationalNaturalInductionDuality : RationalNaturalInductionDualityStatement.{u, v} :=
  rationalNaturalInductionDuality_of_compact_of_modulus
    BruhatTits.dynamicParabolicQuotientCompact
    (rationalParabolicModulus_of_reductiveUnimodularity rationalReductiveUnimodularity
      GroupScheme.dynamicCentralizerReductive)

end Langlands.Aubert.General.RationalPointFamily
