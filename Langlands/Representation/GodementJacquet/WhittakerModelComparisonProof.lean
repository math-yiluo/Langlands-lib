import Langlands.Representation.GodementJacquet.WhittakerModelRationality
import Langlands.Representation.Whittaker.TypeAsymptoticProof
import Langlands.Representation.RankinSelberg.FiniteFunctionMellinProof

/-!
# Matrix-coefficient and Whittaker integrals on the coefficient model

Proof of `WhittakerModelComparisonStatement`: the conditional theorem
`WhittakerTorus.Padic.whittakerModelComparison_of_asymptotics`, applied to the
published proofs of `WhittakerTypeAsymptoticStatement` and
`FiniteFunctionMellinStatement`. See the paired Markdown.
-/

namespace Langlands.GodementJacquet

universe uF uV

/-- JPSS (1983), Section (5.2): on the coefficient model of a representation of
Whittaker type, the matrix-coefficient integrals and the Whittaker integrals span
the same space of rational continuations. -/
theorem whittakerModelComparison : WhittakerModelComparisonStatement.{uF, uV} :=
  WhittakerTorus.Padic.whittakerModelComparison_of_asymptotics
    whittakerTypeAsymptotic RankinSelberg.finiteFunctionMellin

end Langlands.GodementJacquet
