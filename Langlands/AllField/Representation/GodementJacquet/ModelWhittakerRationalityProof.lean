import Langlands.Representation.GodementJacquet.ModelWhittakerRationalityProof
import Langlands.AllField.LocalField.SmoothCharacterNormProofSupplement
import Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllField.Representation.Geometric.GeometricLemmaStatement
import Langlands.AllField.Representation.GodementJacquet.WhittakerModelRationality
import Langlands.AllField.Representation.Parabolic.NormalizedJacquetStatementSupplement
import Langlands.AllField.Representation.RankinSelberg.FiniteFunctionMellinProof
import Langlands.AllField.Representation.Whittaker.TypeAsymptoticProof
/-!
# Convergence and rationality of Whittaker matrix integrals on the model

The conditional coefficient-model theorem is applied to the full Whittaker
torus asymptotic theorem and finite-function Mellin theorem. See the paired
Markdown for the implemented proof and its source provenance.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding ModelWhittakerRationalityStatement WhittakerModelComparisonStatement modelWhittakerRationality whittakerModelComparison_of_rationality
open Langlands.AllField.GodementJacquet

universe uF uV

/-- Every shifted full-matrix Whittaker integral on the coefficient model
converges on a right half-plane and has a rational continuation in `q^(-s)`. -/
theorem modelWhittakerRationality : ModelWhittakerRationalityStatement.{uF, uV} :=
  Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.modelWhittakerRationality.{uF, uV}
    Langlands.AllField.whittakerTypeAsymptotic.{uF, uV}
    Langlands.AllField.RankinSelberg.finiteFunctionMellin.{uF}

end Langlands.AllField.GodementJacquet
