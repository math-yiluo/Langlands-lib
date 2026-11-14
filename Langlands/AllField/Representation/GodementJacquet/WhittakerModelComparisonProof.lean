import Langlands.Representation.GodementJacquet.WhittakerModelComparisonProof
import Langlands.AllField.LocalField.SmoothCharacterNormProofSupplement
import Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllField.Representation.Geometric.GeometricLemmaStatement
import Langlands.AllField.Representation.GodementJacquet.WhittakerModelRationality
import Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatementSupplement
import Langlands.AllField.Representation.RankinSelberg.FiniteFunctionMellinProof
import Langlands.AllField.Representation.Whittaker.TypeAsymptoticProof
/-!
# Matrix-coefficient and Whittaker integrals on the coefficient model

Proof of `WhittakerModelComparisonStatement`: the conditional theorem
`WhittakerTorus.Padic.whittakerModelComparison_of_asymptotics`, applied to the
published proofs of `WhittakerTypeAsymptoticStatement` and
`FiniteFunctionMellinStatement`. See the paired Markdown.
-/

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding ModelWhittakerRationalityStatement WhittakerModelComparisonStatement whittakerModelComparison whittakerModelComparison_of_rationality
open Langlands.AllField.GodementJacquet

universe uF uV

/-- JPSS (1983), Section (5.2): on the coefficient model of a representation of
Whittaker type, the matrix-coefficient integrals and the Whittaker integrals span
the same space of rational continuations. -/
theorem whittakerModelComparison : WhittakerModelComparisonStatement.{uF, uV} :=
  Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.whittakerModelComparison_of_asymptotics
    whittakerTypeAsymptotic Langlands.AllField.RankinSelberg.finiteFunctionMellin

end Langlands.AllField.GodementJacquet
